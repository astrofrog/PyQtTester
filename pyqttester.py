# https://raw.githubusercontent.com/astrofrog/PyQtTester/master/pyqttester.py
#
import re
import sys
import pickle
import logging
from functools import reduce
from collections import namedtuple
from itertools import islice, count
from importlib import import_module

from glue.external.qt import QtGui, QtCore
from glue.external.qt.QtCore import Qt

REAL_EXIT = sys.exit

QT_KEYS = {value: 'Qt.' + key
           for key, value in Qt.__dict__.items()
           if key.startswith('Key_')}
EVENT_TYPE = {v: k
              for k, v in QtCore.QEvent.__dict__.items()
              if isinstance(v, int)}

PathElement = namedtuple('PathElement', ('index', 'type', 'name'))

QWidget = QtGui.QWidget
qApp = QtGui.qApp

SCENARIO_FORMAT_VERSION = 1

log = logging.getLogger(__name__)

def deepgetattr(obj, attr):
    """Recurses through an attribute chain to get the ultimate value."""
    return reduce(getattr, attr.split('.'), obj)


def nth(n, iterable, default=None):
    """Return the n-th item of iterable"""
    return next(islice(iterable, n, None), default)


def typed_nth(n, target_type, iterable, default=None):
    """Return the n-th item of type from iterable"""
    return nth(n, (i for i in iterable if type(i) == target_type), default)

PathElement = namedtuple('PathElement', ('index', 'type', 'name'))


class Resolver:

    class IdentityMapper:
        def __getitem__(self, key):
            return key

    def __init__(self, obj_cache):
        self.id_obj_map = obj_cache if obj_cache is not None else self.IdentityMapper()
        self.obj_id_map = {}
        self.autoinc = count(1)

    @staticmethod
    def _qenum_key(base, value, klass=None):
        """Return Qt enum value as string name of its key.

        Modelled after code by Florian "The Compiler" Bruhin:
        https://github.com/The-Compiler/qutebrowser/blob/master/qutebrowser/utils/debug.py#L91-L167

        Parameters
        ----------
        base: type
            The type object the enum is in, e.g. QFrame or QtCore.Qt.
        value: enum value (int)
            The value of the enum, e.g. Qt.LeftButton
        klass: type
            The enum class the value belongs to, or None to auto-guess.

        Returns
        -------
        key: str
            The key associated with the value if found or '' otherwise.

        Example
        -------
        >>> _qenum_key(Qt, Qt.LeftButton)
        'Qt.LeftButton'
        >>> _qenum_key(Qt, Qt.LeftButton | Qt.RightButton)
        ''
        """
        klass = klass or type(value)

        if klass == int:  # Can't guess enum class of an int
            return ''

        meta_object = getattr(base, 'staticMetaObject', None)
        if meta_object:
            enum = meta_object.indexOfEnumerator(klass.__name__)
            key = meta_object.enumerator(enum).valueToKey(value)
        else:
            try:
                key = next(name for name, obj in base.__dict__.items()
                           if isinstance(obj, klass) and obj == value)
            except StopIteration:
                key = ''
        return (base.__name__ + '.' + key) if key else ''

    @classmethod
    def _qflags_key(cls, base, value, klass=None):
        """Convert a Qt QFlags value to its keys as '|'-separated string.

        Modelled after code by Florian "The Compiler" Bruhin:
        https://github.com/The-Compiler/qutebrowser/blob/master/qutebrowser/utils/debug.py#L91-L167

        Parameters
        ----------
        base: type
            The type object the flags are in, e.g. QtCore.Qt
        value: int
            The flags value to convert to string.
        klass: type
            The flags class the value belongs to, or None to auto-guess.

        Returns
        -------
        keys: str
            The keys associated with the flags as a '|'-separated string
            if they were found; '' otherwise.

        Note
        ----
        Passing a combined value (e.g. Qt.AlignCenter) will get the names
        of the individual bits (Qt.AlignVCenter | Qt.AlignHCenter).

        Bugs
        ----
        https://github.com/The-Compiler/qutebrowser/issues/42
        """
        klass = klass or type(value)
        if klass == int:
            return ''
        if klass.__name__.endswith('s'):
            klass = getattr(base, klass.__name__[:-1])
        keys = []
        mask = 1
        value = int(value)
        while mask <= value:
            if value & mask:
                keys.append(cls._qenum_key(base, klass(mask), klass=klass))
            mask <<= 1
        if not keys and value == 0:
            keys.append(cls._qenum_key(base, klass(0), klass=klass))
        return '|'.join([k for k in keys if k])

    @classmethod
    def _serialize_value(cls, value, attr):
        """Return str representation of value for attribute attr."""
        value_type = type(value)
        if value_type == int:
            if attr == 'key':
                return QT_KEYS[value]
            return str(value)
        if value_type == str:
            return repr(value)
        if value_type == bool:
            return str(value)
        # QPoint/QRect (...) values are pickleable directly according to PyQt
        # docs. The reason they are not used like this here is consistency and
        # smaller size. Yes, this string is >100% more light-weight.
        if isinstance(value, (QtCore.QPointF, QtCore.QPoint)):
            return 'QtCore.{}({}, {})'.format(type(value).__name__,
                                              value.x(),
                                              value.y())
        if isinstance(value, (QtCore.QRectF, QtCore.QRect)):
            return 'QtCore.{}({}, {}, {}, {})'.format(type(value).__name__,
                                                      value.x(),
                                                      value.y(),
                                                      value.width(),
                                                      value.height())
        # Perhaps it's an enum value from Qt namespace
        assert isinstance(Qt.LeftButton, int)
        if isinstance(value, int):
            s = cls._qenum_key(Qt, value)
            if s: return s
        # Finally, if it ends with 's', it's probably a QFlags object
        # combining the flags of associated Qt.<name-without-s> type, e.g.
        # bitwise or-ing Qt.MouseButton values (Qt.LeftButton | Qt.RightButton)
        # makes a Qt.MouseButtons object:
        assert isinstance((Qt.LeftButton | Qt.RightButton), Qt.MouseButtons)
        if type(value).__name__.endswith('s'):
            s = cls._qflags_key(Qt, value)
            if s:
                return s

        raise ValueError

    EVENT_ATTRIBUTES = {
        # Q*Event attributes, ordered as the constructor takes them
        'QMouseEvent':'type pos globalPos button buttons modifiers'.split(),
        'QKeyEvent': 'type key modifiers text isAutoRepeat count'.split(),
        'QMoveEvent': 'pos oldPos'.split(),
        'QCloseEvent': [],
    }

    @classmethod
    def serialize_event(cls, event):
        assert isinstance(event, QtCore.QEvent)

        event_type = type(event)
        event_attributes = cls.EVENT_ATTRIBUTES.get(event_type.__name__, ('type',))
        if not event_attributes:
            log.warning('Missing fingerprint for event: %s, type=%s, mro=%s',
                        event_type, event.type(), event_type.__mro__)

        args = []
        if event_attributes and event_attributes[0] == 'type':
            args.append('QtCore.' + cls._qenum_key(QtCore.QEvent, event.type()))
            # Skip first element (type) in the loop ahead
            event_attributes = iter(event_attributes); next(event_attributes)
        for attr in event_attributes:
            value = getattr(event, attr)()
            try:
                args.append(cls._serialize_value(value, attr))
            except ValueError:
                args.append('0b0')
                log.warning("Can't serialize object %s of type %s "
                            "for attribute %s. Inserting a 0b0 (zero) instead.",
                            value, type(value).__mro__, attr)
        event_str = event_type.__name__ + '(' + ', '.join(args) + ')'
        log.info('Serialized event: %s', event_str)
        return event_str

    @staticmethod
    def deserialize_event(event_str):
        try:
            return eval('QtGui.' + event_str)
        except AttributeError:
            return eval('QtCore.' + event_str)

    @staticmethod
    def serialize_type(type_obj):
        """Return fully-qualified name of type, or '' if translation not reversible"""
        type_str = type_obj.__module__ + ':' + type_obj.__qualname__
        return type_str if '.<locals>.' not in type_str else ''

    @staticmethod
    def deserialize_type(type_str):
        """Return type object that corresponds to type_str"""
        module, qualname = type_str.split(':')
        return deepgetattr(import_module(module), qualname)

    @classmethod
    def _get_children(cls, widget):
        """
        Get all children widgets of widget. Children are if they're in widget's
        layout, or if the widget splits them, or if they are QObject children
        of widget, or similar.
        """
        if widget is None:
            for item in qApp.topLevelWidgets():
                yield qApp.topLevelWidgets()

        if isinstance(widget, QtGui.QSplitter):
            for i in range(widget.count()):
                yield widget.widget(i)
                yield widget.handle(i)

        layout = hasattr(widget, 'layout') and widget.layout()
        if layout:
            for i in range(layout.count()):
                yield layout.itemAt(i).widget()

        if hasattr(widget, 'children'):
            for child in widget.children():
                yield child

        # If widget can't be found in the hierarchy by Qt means,
        # try Python object attributes
        for attr in dir(widget):
            if not attr.startswith('__') and attr.endswith('__'):
                yield getattr(widget, attr)

    @classmethod
    def serialize_object(cls, obj):
        assert isinstance(obj, QWidget)

        path = []
        parent = obj
        while parent is not None:
            widget, parent = parent, parent.parentWidget()
            children = cls._get_children(parent)
            # This typed index is more resilient than simple layout.indexOf()
            typed_widgets = (w for w in children if type(w) == type(widget))
            index = next((i for i, w in enumerate(typed_widgets) if w is widget), None)

            if index is None:
                # FIXME: What to do here instead?
                if path:
                    log.warning('Skipping object path: %s -> %s', obj,
                                path)
                path = ()
                break
            path.append(PathElement(index,
                                    cls.serialize_type(type(widget)),
                                    widget.objectName()))
        assert (not path or
                len(path) > 1 or
                len(path) == 1 and obj in qApp.topLevelWidgets())
        if path:
            path = tuple(reversed(path))
            log.info('Serialized object path: %s', path)
        return path

    @classmethod
    def _find_by_name(cls, target):
        return (qApp.findChild(cls.deserialize_type(target.type), target.name) or
                next(widget for widget in qApp.allWidgets()
                     if widget.objectName() == target.name))

    @classmethod
    def deserialize_object(cls, path):
        target = path[-1]

        # Find target object by name
        if target.name:
            try:
                return cls._find_by_name(target)
            except StopIteration:
                log.warning('Name "%s" provided, but no *widget* with that name '
                            'found. If the test passes, its result might be '
                            'invalid, or the test may just need updating.',
                            target.name)

        # If target widget doesn't have a name, find it in the tree
        def get_child(i, widgets):
            element = path[i]
            widget = typed_nth(element.index,
                               cls.deserialize_type(element.type),
                               widgets)
            if element == target or widget is None:
                return widget
            return get_child(i + 1, cls._get_children(widget))

        return get_child(0, qApp.topLevelWidgets())

    def getstate(self, obj, event):
        """Return picklable state of the object and its event"""
        obj_path = self.serialize_object(obj)
        if not obj_path:
            log.warning('Skipping object: %s', obj)
            return None
        event_str = self.serialize_event(event)
        if not event_str:
            log.warning('Skipping event: %s', event)

        obj_id = self.obj_id_map.get(obj_path)
        if obj_id is None:
            obj_id = next(self.autoinc)
            self.obj_id_map[obj_path] = obj_id
            self.id_obj_map[obj_id] = obj_path
        return (obj_id, event_str)

    def setstate(self, obj_id, event_str):
        obj_path = self.id_obj_map[obj_id]
        obj = self.deserialize_object(obj_path)
        if obj is None:
            log.error("Can't replay event %s on object %s: Object not found",
                      event_str, obj_path)
            REAL_EXIT(3)
        event = self.deserialize_event(event_str)
        log.info('Replaying event %s on object %s',
                 event_str, obj_path)
        return qApp.sendEvent(obj, event)

    def print_state(self, i, obj_id, event_str):
        obj_path = self.id_obj_map[obj_id]
        print('Event', str(i) + ':', event_str.replace('QtCore.', ''))
        print('Object:')
        for indent, el in enumerate(obj_path):
            print('  '*(indent + 1),
                  el.index,
                  repr(el.name) if el.name else '',
                  el.type)
        print()


class _EventFilter:

    @staticmethod
    def wait_for_app_start(method):
        is_started = False

        def wrapper(self, obj, event):

            global is_started
            if not is_started:
                log.debug('Caught %s (%s) event but app not yet fully "started"',
                          EVENT_TYPE.get(event.type(),
                                         'QEvent(type=' + str(event.type()) + ')'),
                          type(event).__name__)
                if event.type() == QtCore.QEvent.ActivationChange:
                    log.debug("Ok, app is started now, don't worry")
                    is_started = True
            # With the following return in place, Xvfb sometimes got stuck
            # before any serious events happened. I suspected WM (or lack
            # thereof) being the culprit, so now we spawn a WM that sends
            # focus, activation events, ... This seems to have fixed it once.
            # I think this return (False) should be here (instead of proceeding
            # with the filter method).
            return method(self, obj, event) if is_started else False
        return wrapper

    def close(self):
        pass


class EventRecorder(_EventFilter, QtCore.QObject):

    def __init__(self, file, events_include, events_exclude):
        super().__init__()
        self.file = file

        # Prepare the recorded events stack;
        # the first entry is the protocol version
        self.events = [SCENARIO_FORMAT_VERSION]
        obj_cache = {}
        self.events.append(obj_cache)

        self.resolver = Resolver(obj_cache)

        is_included = (re.compile('|'.join(events_include.split(','))).search
                       if events_include else lambda _: True)
        is_excluded = (re.compile('|'.join(events_exclude.split(','))).search
                       if events_exclude else lambda _: False)

        def event_matches(event_name):
            return is_included(event_name) and not is_excluded(event_name)

        self.event_matches = event_matches

    @_EventFilter.wait_for_app_start
    def eventFilter(self, obj, event):
        # Only process out-of-application, system (e.g. X11) events
        # if not event.spontaneous():
        #     return False
        is_skipped = (not self.event_matches(type(event).__name__) or
                      not isinstance(obj, QWidget))  # FIXME: This condition is too strict (QGraphicsItems are QOjects)
        log_ = log.debug if is_skipped else log.info
        log_('Caught %s%s %s event (%s) on object %s',
             'skipped' if is_skipped else 'recorded',
             ' spontaneous' if event.spontaneous() else '',
             EVENT_TYPE.get(event.type(),
                            'Unknown(type=' + str(event.type()) + ')'),
             event.__class__.__name__, obj)
        # Before any event on any widget, make sure the window of that widget
        # is active and raised (in front). This is required for replaying
        # without a window manager.
        if (isinstance(obj, QWidget) and
                event.type() == QtCore.QEvent.MouseButtonPress and
                not is_skipped and
                not obj.isActiveWindow() and
                event.spontaneous()):
            obj.activateWindow()
        if not is_skipped:
            serialized = self.resolver.getstate(obj, event)
            if serialized:
                self.events.append(serialized)
        return False

    def close(self):
        """Write out the scenario"""
        log.debug('Writing scenario file')
        pickle.dump(self.events, self.file, protocol=0)
        log.info("Scenario of %d events written into '%s'",
                 len(self.events) - SCENARIO_FORMAT_VERSION - 1, self.file.name)
        log.debug(self.events)


class EventReplayer(_EventFilter, QtCore.QObject):

    def __init__(self, file):
        super().__init__()
        # Replay events X ms after the last event
        self.timer = QtCore.QTimer(self, interval=50)
        self.timer.timeout.connect(self.replay_next_event)
        self.load(file)

    def load(self, file):
        self._events = pickle.load(file)
        self.events = iter(self._events)
        format_version = next(self.events)
        obj_cache = next(self.events) if format_version > 0 else None
        self.resolver = Resolver(obj_cache)

    @_EventFilter.wait_for_app_start
    def eventFilter(self, _, event):
        if (event.type() == QtCore.QEvent.Timer and
                event.timerId() == self.timer.timerId()):
            # Skip self's timer events
            return False
        log.debug('Caught %s (%s) event; resetting timer',
                  EVENT_TYPE.get(event.type(), 'Unknown(type=' + str(event.type()) + ')'),
                  type(event))
        self.timer.stop()
        self.timer.start()
        return False

    def replay_next_event(self):
        # TODO: if timer took too long (significantly more than its interval)
        # perhaps there was a busy loop in the code; better restart it
        self.timer.stop()
        event = next(self.events, None)
        if not event:
            log.info('No more events to replay.')
            QtGui.qApp.quit()
            return
        log.debug('Replaying event: %s', event)
        self.resolver.setstate(*event)
        return False

    def close(self):
        remaining_events = list(self.events)
        if remaining_events:
            log.warning("Application didn't manage to replay all events. "
                        "This may indicate failure. But not necessarily. :|")
            log.info("The remaining events are: %s", remaining_events)
