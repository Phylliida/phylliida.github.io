




/*
     FILE ARCHIVED ON 9:13:05 Jul 21, 2011 AND RETRIEVED FROM THE
     INTERNET ARCHIVE ON 22:02:05 Mar 14, 2017.
     JAVASCRIPT APPENDED BY WAYBACK MACHINE, COPYRIGHT INTERNET ARCHIVE.

     ALL OTHER CONTENT MAY ALSO BE PROTECTED BY COPYRIGHT (17 U.S.C.
     SECTION 108(a)(3)).
*/
// Generated: Wed Dec 31 00:57:24 2008

(function () {

;
// ##########################
// File: /ext/json2.js
// ##########################
/*
    /web/20110721091305/http://www.JSON.org/json2.js
    2008-10-31

    Public Domain.

    NO WARRANTY EXPRESSED OR IMPLIED. USE AT YOUR OWN RISK.

    See /web/20110721091305/http://www.JSON.org/js.html

    This file creates a global JSON object containing two methods: stringify
    and parse.

        JSON.stringify(value, replacer, space)
            value       any JavaScript value, usually an object or array.

            replacer    an optional parameter that determines how object
                        values are stringified for objects. It can be a
                        function or an array of strings.

            space       an optional parameter that specifies the indentation
                        of nested structures. If it is omitted, the text will
                        be packed without extra whitespace. If it is a number,
                        it will specify the number of spaces to indent at each
                        level. If it is a string (such as '\t' or '&nbsp;'),
                        it contains the characters used to indent at each level.

            This method produces a JSON text from a JavaScript value.

            When an object value is found, if the object contains a toJSON
            method, its toJSON method will be called and the result will be
            stringified. A toJSON method does not serialize: it returns the
            value represented by the name/value pair that should be serialized,
            or undefined if nothing should be serialized. The toJSON method
            will be passed the key associated with the value, and this will be
            bound to the object holding the key.

            For example, this would serialize Dates as ISO strings.

                Date.prototype.toJSON = function (key) {
                    function f(n) {
                        // Format integers to have at least two digits.
                        return n < 10 ? '0' + n : n;
                    }

                    return this.getUTCFullYear()   + '-' +
                         f(this.getUTCMonth() + 1) + '-' +
                         f(this.getUTCDate())      + 'T' +
                         f(this.getUTCHours())     + ':' +
                         f(this.getUTCMinutes())   + ':' +
                         f(this.getUTCSeconds())   + 'Z';
                };

            You can provide an optional replacer method. It will be passed the
            key and value of each member, with this bound to the containing
            object. The value that is returned from your method will be
            serialized. If your method returns undefined, then the member will
            be excluded from the serialization.

            If the replacer parameter is an array of strings, then it will be
            used to select the members to be serialized. It filters the results
            such that only members with keys listed in the replacer array are
            stringified.

            Values that do not have JSON representations, such as undefined or
            functions, will not be serialized. Such values in objects will be
            dropped; in arrays they will be replaced with null. You can use
            a replacer function to replace those with JSON values.
            JSON.stringify(undefined) returns undefined.

            The optional space parameter produces a stringification of the
            value that is filled with line breaks and indentation to make it
            easier to read.

            If the space parameter is a non-empty string, then that string will
            be used for indentation. If the space parameter is a number, then
            the indentation will be that many spaces.

            Example:

            text = JSON.stringify(['e', {pluribus: 'unum'}]);
            // text is '["e",{"pluribus":"unum"}]'


            text = JSON.stringify(['e', {pluribus: 'unum'}], null, '\t');
            // text is '[\n\t"e",\n\t{\n\t\t"pluribus": "unum"\n\t}\n]'

            text = JSON.stringify([new Date()], function (key, value) {
                return this[key] instanceof Date ?
                    'Date(' + this[key] + ')' : value;
            });
            // text is '["Date(---current time---)"]'


        JSON.parse(text, reviver)
            This method parses a JSON text to produce an object or array.
            It can throw a SyntaxError exception.

            The optional reviver parameter is a function that can filter and
            transform the results. It receives each of the keys and values,
            and its return value is used instead of the original value.
            If it returns what it received, then the structure is not modified.
            If it returns undefined then the member is deleted.

            Example:

            // Parse the text. Values that look like ISO date strings will
            // be converted to Date objects.

            myData = JSON.parse(text, function (key, value) {
                var a;
                if (typeof value === 'string') {
                    a =
/^(\d{4})-(\d{2})-(\d{2})T(\d{2}):(\d{2}):(\d{2}(?:\.\d*)?)Z$/.exec(value);
                    if (a) {
                        return new Date(Date.UTC(+a[1], +a[2] - 1, +a[3], +a[4],
                            +a[5], +a[6]));
                    }
                }
                return value;
            });

            myData = JSON.parse('["Date(09/09/2001)"]', function (key, value) {
                var d;
                if (typeof value === 'string' &&
                        value.slice(0, 5) === 'Date(' &&
                        value.slice(-1) === ')') {
                    d = new Date(value.slice(5, -1));
                    if (d) {
                        return d;
                    }
                }
                return value;
            });


    This is a reference implementation. You are free to copy, modify, or
    redistribute.

    This code should be minified before deployment.
    See /web/20110721091305/http://javascript.crockford.com/jsmin.html

    USE YOUR OWN COPY. IT IS EXTREMELY UNWISE TO LOAD CODE FROM SERVERS YOU DO
    NOT CONTROL.
*/

/*jslint evil: true */

/*global JSON */

/*members "", "\b", "\t", "\n", "\f", "\r", "\"", JSON, "\\", call,
    charCodeAt, getUTCDate, getUTCFullYear, getUTCHours, getUTCMinutes,
    getUTCMonth, getUTCSeconds, hasOwnProperty, join, lastIndex, length,
    parse, propertyIsEnumerable, prototype, push, replace, slice, stringify,
    test, toJSON, toString, valueOf
*/

// Create a JSON object only if one does not already exist. We create the
// methods in a closure to avoid creating global variables.

//


// MOdified

 var JSON = {};
(function () {

    function f(n) {
        // Format integers to have at least two digits.
        return n < 10 ? '0' + n : n;
    }

    if (typeof Date.prototype.toJSON !== 'function') {

        Date.prototype.toJSON = function (key) {

            return this.getUTCFullYear()   + '-' +
                 f(this.getUTCMonth() + 1) + '-' +
                 f(this.getUTCDate())      + 'T' +
                 f(this.getUTCHours())     + ':' +
                 f(this.getUTCMinutes())   + ':' +
                 f(this.getUTCSeconds())   + 'Z';
        };

        String.prototype.toJSON =
        Number.prototype.toJSON =
        Boolean.prototype.toJSON = function (key) {
            return this.valueOf();
        };
    }

    var cx = /[\u0000\u00ad\u0600-\u0604\u070f\u17b4\u17b5\u200c-\u200f\u2028-\u202f\u2060-\u206f\ufeff\ufff0-\uffff]/g,
        escapable = /[\\\"\x00-\x1f\x7f-\x9f\u00ad\u0600-\u0604\u070f\u17b4\u17b5\u200c-\u200f\u2028-\u202f\u2060-\u206f\ufeff\ufff0-\uffff]/g,
        gap,
        indent,
        meta = {    // table of character substitutions
            '\b': '\\b',
            '\t': '\\t',
            '\n': '\\n',
            '\f': '\\f',
            '\r': '\\r',
            '"' : '\\"',
            '\\': '\\\\'
        },
        rep;


    function quote(string) {

// If the string contains no control characters, no quote characters, and no
// backslash characters, then we can safely slap some quotes around it.
// Otherwise we must also replace the offending characters with safe escape
// sequences.

        escapable.lastIndex = 0;
        return escapable.test(string) ?
            '"' + string.replace(escapable, function (a) {
                var c = meta[a];
                if (typeof c === 'string') {
                    return c;
                }
                return '\\u' + ('0000' + a.charCodeAt(0).toString(16)).slice(-4);
            }) + '"' :
            '"' + string + '"';
    }


    function str(key, holder) {

// Produce a string from holder[key].

        var i,          // The loop counter.
            k,          // The member key.
            v,          // The member value.
            length,
            mind = gap,
            partial,
            value = holder[key];

// If the value has a toJSON method, call it to obtain a replacement value.

        if (value && typeof value === 'object' &&
                typeof value.toJSON === 'function') {
            value = value.toJSON(key);
        }

// If we were called with a replacer function, then call the replacer to
// obtain a replacement value.

        if (typeof rep === 'function') {
            value = rep.call(holder, key, value);
        }

// What happens next depends on the value's type.

        switch (typeof value) {
        case 'string':
            return quote(value);

        case 'number':

// JSON numbers must be finite. Encode non-finite numbers as null.

            return isFinite(value) ? String(value) : 'null';

        case 'boolean':
        case 'null':

// If the value is a boolean or null, convert it to a string. Note:
// typeof null does not produce 'null'. The case is included here in
// the remote chance that this gets fixed someday.

            return String(value);

// If the type is 'object', we might be dealing with an object or an array or
// null.

        case 'object':

// Due to a specification blunder in ECMAScript, typeof null is 'object',
// so watch out for that case.

            if (!value) {
                return 'null';
            }

// Make an array to hold the partial results of stringifying this object value.

            gap += indent;
            partial = [];

// If the object has a dontEnum length property, we'll treat it as an array.

            if (typeof value.length === 'number' &&
                    !value.propertyIsEnumerable('length')) {

// The object is an array. Stringify every element. Use null as a placeholder
// for non-JSON values.

                length = value.length;
                for (i = 0; i < length; i += 1) {
                    partial[i] = str(i, value) || 'null';
                }

// Join all of the elements together, separated with commas, and wrap them in
// brackets.

                v = partial.length === 0 ? '[]' :
                    gap ? '[\n' + gap +
                            partial.join(',\n' + gap) + '\n' +
                                mind + ']' :
                          '[' + partial.join(',') + ']';
                gap = mind;
                return v;
            }

// If the replacer is an array, use it to select the members to be stringified.

            if (rep && typeof rep === 'object') {
                length = rep.length;
                for (i = 0; i < length; i += 1) {
                    k = rep[i];
                    if (typeof k === 'string') {
                        v = str(k, value);
                        if (v) {
                            partial.push(quote(k) + (gap ? ': ' : ':') + v);
                        }
                    }
                }
            } else {

// Otherwise, iterate through all of the keys in the object.

                for (k in value) {
                    if (Object.hasOwnProperty.call(value, k)) {
                        v = str(k, value);
                        if (v) {
                            partial.push(quote(k) + (gap ? ': ' : ':') + v);
                        }
                    }
                }
            }

// Join all of the member texts together, separated with commas,
// and wrap them in braces.

            v = partial.length === 0 ? '{}' :
                gap ? '{\n' + gap + partial.join(',\n' + gap) + '\n' +
                        mind + '}' : '{' + partial.join(',') + '}';
            gap = mind;
            return v;
        }
    }

// If the JSON object does not yet have a stringify method, give it one.

    if (typeof JSON.stringify !== 'function') {
        JSON.stringify = function (value, replacer, space) {

// The stringify method takes a value and an optional replacer, and an optional
// space parameter, and returns a JSON text. The replacer can be a function
// that can replace values, or an array of strings that will select the keys.
// A default replacer method can be provided. Use of the space parameter can
// produce text that is more easily readable.

            var i;
            gap = '';
            indent = '';

// If the space parameter is a number, make an indent string containing that
// many spaces.

            if (typeof space === 'number') {
                for (i = 0; i < space; i += 1) {
                    indent += ' ';
                }

// If the space parameter is a string, it will be used as the indent string.

            } else if (typeof space === 'string') {
                indent = space;
            }

// If there is a replacer, it must be a function or an array.
// Otherwise, throw an error.

            rep = replacer;
            if (replacer && typeof replacer !== 'function' &&
                    (typeof replacer !== 'object' ||
                     typeof replacer.length !== 'number')) {
                throw new Error('JSON.stringify');
            }

// Make a fake root object containing our value under the key of ''.
// Return the result of stringifying the value.

            return str('', {'': value});
        };
    }


// If the JSON object does not yet have a parse method, give it one.

    if (typeof JSON.parse !== 'function') {
        JSON.parse = function (text, reviver) {

// The parse method takes a text and an optional reviver function, and returns
// a JavaScript value if the text is a valid JSON text.

            var j;

            function walk(holder, key) {

// The walk method is used to recursively walk the resulting structure so
// that modifications can be made.

                var k, v, value = holder[key];
                if (value && typeof value === 'object') {
                    for (k in value) {
                        if (Object.hasOwnProperty.call(value, k)) {
                            v = walk(value, k);
                            if (v !== undefined) {
                                value[k] = v;
                            } else {
                                delete value[k];
                            }
                        }
                    }
                }
                return reviver.call(holder, key, value);
            }


// Parsing happens in four stages. In the first stage, we replace certain
// Unicode characters with escape sequences. JavaScript handles many characters
// incorrectly, either silently deleting them, or treating them as line endings.

            cx.lastIndex = 0;
            if (cx.test(text)) {
                text = text.replace(cx, function (a) {
                    return '\\u' +
                        ('0000' + a.charCodeAt(0).toString(16)).slice(-4);
                });
            }

// In the second stage, we run the text against regular expressions that look
// for non-JSON patterns. We are especially concerned with '()' and 'new'
// because they can cause invocation, and '=' because it can cause mutation.
// But just to be safe, we want to reject all unexpected forms.

// We split the second stage into 4 regexp operations in order to work around
// crippling inefficiencies in IE's and Safari's regexp engines. First we
// replace the JSON backslash pairs with '@' (a non-JSON character). Second, we
// replace all simple value tokens with ']' characters. Third, we delete all
// open brackets that follow a colon or comma or that begin the text. Finally,
// we look to see that the remaining characters are only whitespace or ']' or
// ',' or ':' or '{' or '}'. If that is so, then the text is safe for eval.

            if (/^[\],:{}\s]*$/.
test(text.replace(/\\(?:["\\\/bfnrt]|u[0-9a-fA-F]{4})/g, '@').
replace(/"[^"\\\n\r]*"|true|false|null|-?\d+(?:\.\d*)?(?:[eE][+\-]?\d+)?/g, ']').
replace(/(?:^|:|,)(?:\s*\[)+/g, ''))) {

// In the third stage we use the eval function to compile the text into a
// JavaScript structure. The '{' operator is subject to a syntactic ambiguity
// in JavaScript: it can begin a block or an object literal. We wrap the text
// in parens to eliminate the ambiguity.

                j = eval('(' + text + ')');

// In the optional fourth stage, we recursively walk the new structure, passing
// each name/value pair to a reviver function for possible transformation.

                return typeof reviver === 'function' ?
                    walk({'': j}, '') : j;
            }

// If the text is not JSON parseable, then a SyntaxError is thrown.

            throw new SyntaxError('JSON.parse');
        };
    }
})();

;
// ##########################
// File: /ext/joose.js
// ##########################
// Generated: Sun Nov 16 17:19:56 2008


// ##########################
// File: Joose.js
// ##########################
var joosetop = this;

Joose = function () {
    this.cc              = null;  // the current class
    this.currentModule   = null
    this.top             = joosetop;
    this.globalObjects   = [];
    
    this.anonymouseClassCounter = 0;
};

// Static helpers for Arrays
Joose.A = {};
Joose.A.each = function (array, func) {
    for(var i = 0; i < array.length; i++) {
        func(array[i], i)
    }
}
Joose.A.exists = function (array, value) {
    for(var i = 0; i < array.length; i++) {
        if(array[i] == value) {
            return true
        }
    }
    return false
}
Joose.A.concat = function (source, array) {
    source.push.apply(source, array)
    return source
}

Joose.A.grep = function (array, func) {
    var a = [];
    Joose.A.each(array, function (t) {
        if(func(t)) {
            a.push(t)
        }
    })
    return a
}
Joose.A.remove = function (array, removeEle) {
    var a = [];
    Joose.A.each(array, function (t) {
        if(t !== removeEle) {
            a.push(t)
        }
    })
    return a
}

// Static helpers for Strings
Joose.S = {};
Joose.S.uppercaseFirst = function (string) { 
    var first = string.substr(0,1);
    var rest  = string.substr(1,string.length-1);
    first = first.toUpperCase()
    return first + rest;
}

Joose.S.isString = function (thing) { 
    if(typeof thing == "string") {
        return true
    }
    return false
}

// Static helpers for objects
Joose.O = {};
Joose.O.each = function (object, func) {
    for(var i in object) {
        func(object[i], i)
    }
}

Joose.O.eachSafe = function (object, func) {
    for(var i in object) {
        if(object.hasOwnProperty(i)) {
            func(object[i], i)
        }
    }
}

// Experimental!
Joose.O.extend = function (target, newObject) {
    for(var i in newObject) {
        var thing = newObject[i]
        target[i] = thing
    }
}


Joose.prototype = {
    
    addToString: function (object, func) {
        object.toString = func;
    },
    
    /*
     * Differentiates between instances and classes
     */
    isInstance: function(obj) {
        if(!obj.meta) {
            throw "isInstance only works with Joose objects and classes."
        }
        if(obj.constructor === obj.meta.c) {
            return true
        }
        return false
    },
    
    init: function () {
        this.builder = new Joose.Builder();
        this.builder.globalize()
    },
    // this needs to be updated in release.pl too, if files are added
    components: function () {
        return [
            "Joose.Builder",
            "Joose.Class",
            "Joose.Method",
            "Joose.ClassMethod",
            "Joose.Attribute",
            "Joose.Role",
            "Joose.SimpleRequest",
            "Joose.Gears",
            "Joose.Storage",
            "Joose.Storage.Unpacker",
            "Joose.Decorator",
            "Joose.Module",
            "Joose.Prototype",
            "Joose.TypeConstraint",
            "Joose.TypeCoercion",
            "Joose.Types"
        ]
    },

    loadComponents: function (basePath) {
        var html = "";
        Joose.A.each(this.components(), function (name) {
            var url    = ""+basePath + "/" + name.split(".").join("/") + ".js";
           
            html += '<script type="text/javascript" src="'+url+'"></script>'
        })
        document.write(html)
    }
}

Joose.copyObject = function (source, target) {
    var keys = "";
    Joose.O.each(source, function (value, name) {  keys+=", "+name; target[name] = value })
    return target
};



Joose.emptyFunction = function () {};

var joose = new Joose();


Joose.bootstrap = function () {
    // Bootstrap
    var BOOT = new Joose.MetaClassBootstrap(); 
    
    BOOT.builder    = Joose.MetaClassBootstrap;

    Joose.MetaClass = BOOT.createClass("Joose.MetaClass");
   
    Joose.MetaClass.meta.addNonJooseSuperClass("Joose.MetaClassBootstrap", BOOT)
    
    Joose.MetaClass.meta.addMethod("initialize", function () { this._name = "Joose.MetaClass" })

    var META     = new Joose.MetaClass();
    
    META.builder = Joose.MetaClass;
    
    Joose.Class  = META.createClass("Joose.Class")
    Joose.Class.meta.addSuperClass(Joose.MetaClass);
    Joose.MetaClass.meta.addMethod("initialize", function () { this._name = "Joose.Class" })
}

Joose.bootstrap2 = function () {
    // Turn Joose.Method into a Joose.Class object
    Joose.Builder.Globals.joosify("Joose.Method", Joose.Method)
    Joose.Builder.Globals.joosify("Joose.Attribute", Joose.Attribute)
}

Joose.bootstrap3 = function () {
    // make the .meta object circular
}

/**
 * @name Joose.Class
 * @constructor
 */
/*
 * Joose.MetaClassBootstrap is used to bootstrap the Joose.Class with a regular JS constructor
 */
/** ignore */ // Do not display the Bootstrap classes in the docs
Joose.MetaClassBootstrap = function () {
    this._name            = "Joose.MetaClassBootstrap";
    this.methodNames      = [];
    this.attributeNames   = ["_name", "isAbstract", "isDetached", "methodNames", "attributeNames", "methods", "parentClasses", "roles", "c"];
    this.attributes       = {},
    this.methods          = {};
    this.classMethods     = {};
    this.parentClasses    = [];
    this.roles            = []; // All roles
    this.myRoles          = []; // Only roles applied to me directly
    this.isAbstract       = false;
    this.isDetached       = false;
}
/** @ignore */
Joose.MetaClassBootstrap.prototype = {
    
    toString: function () {
        if(this.meta) {
            return "a "+this.meta.className();
        }
        return "NoMeta"
    },
    
    /**
     * Returns the name of the class
     * @name className
     * @function
     * @memberof Joose.Class
     */
    /** @ignore */
    className: function () {
        return this._name
    },
    
    /**
     * Returns the name of the class (alias to className())
     * @name getName
     * @function
     * @memberof Joose.Class
     */
    /** @ignore */
    getName: function () {
        return this.className()
    },
    
    /**
     * Creates a new empty meta class object
     * @function
     * @name newMetaClass
     * @memberof Joose.Class
     */
    /** @ignore */
    newMetaClass: function () {
        
        var me  = this;
        
        var metaClassClass = this.builder;
        
        var c     = new metaClassClass();
        c.builder = metaClassClass;
        c._name   = this._name
        
        c.methodNames    = [];
        c.attributeNames = [];
        c.methods        = {};
        c.classMethods   = {};
        c.parentClasses  = [];
        c.roles          = [];
        c.myRoles        = [];
        c.attributes     = {};
        
        var myMeta = this.meta;
        if(!myMeta) {
            myMeta = this;
        }
        
        c.meta = myMeta
        
        return c
    },
    
    /**
     * Creates a new class object
     * @function
     * @name createClass
     * @param {function} optionalConstructor If provided will be used as the class constructor (You should not need this)
     * @param {Joose.Module} optionalModuleObject If provided the Module's name will be prepended to the class name 
     * @memberof Joose.Class
     */
    /** @ignore */
    createClass:    function (name, optionalConstructor, optionalModuleObject) {
        var meta  = this.newMetaClass();
        
        var c;
        
        if(optionalConstructor) {
            c = optionalConstructor
        } else {
            c = this.defaultClassFunctionBody()
            
            if(optionalModuleObject) {
                optionalModuleObject.addElement(c)
                // meta.setModule(optionalModuleObject)
            }
        }
        
        c.prototype.meta = meta
        c.meta    = meta;
        if(name == null) {
            meta._name = "__anonymous__" 
        } else {
            var className = name;
            if(optionalModuleObject) {
                className = optionalModuleObject.getName() + "." + name
            }
            meta._name = className;
        }
        meta.c = c;
        
        // store them in the global object if they have no namespace
        // They will end up in the Module __JOOSE_GLOBAL__
        if(!optionalModuleObject) {
            // Because the class Joose.Module might not exist yet, we use this temp store
            // that will later be in the global module
            joose.globalObjects.push(c)
        }
        
        meta.addInitializer();
        meta.addToString();
        meta.addDetacher();
        
        return c;
    },
    
    buildComplete: function () {
        // may be overriden in sublass
    },
    
    // intializes a class from the class definitions
    initializeFromProps: function (props) {
        this._initializeFromProps(props)
    },
    
    _initializeFromProps: function (props) {
        var me = this;
        if(props) {
            
            if(joose.top.CHAOTIC_TRAVERSION_ORDER) {
                Joose.A.each(["isa", "does", "has", "method", "methods"], function (name) {
                    if(name in props) {
                        var value = props[name];
                        me._initializeFromProp(name, value, props)
                        delete props[name]
                    }
                })
            }
            
            // For each property of the class constructor call the builder
            Joose.O.eachSafe(props, function (value, name) {
                me._initializeFromProp(name, value, props)
            })
            
            for(var i = 0; i < this.roles.length; i++) {
                var role = this.roles[i];
                role.meta.applyMethodModifiers(this.c)
            }
            
            me.buildComplete();     
            me.validateClass();
        }
    },
    
    _initializeFromProp: function (propName, value, props) {
        var paras             = value;
        var customBuilderName = "handleProp"+propName;
        // if the meta class of the current class implements handleProp+nameOfBuilder we use that
        if(this.meta.can(customBuilderName)) {
            this[customBuilderName](paras, props)
        } else { // Otherwise use a builder from this file
            throw new Error("Called invalid builder "+propName+" while creating class "+this.className())
        }
    },
    
    /**
     * Returns a new instance of the class that this meta class instance is representing
     * @function
     * @name instantiate
     * @memberof Joose.Class
     */    
    instantiate: function () {
        //var o = new this.c.apply(this, arguments);
    
        // Ough! Calling a constructor with arbitrary arguments hack
        var f = function () {};
        f.prototype = this.c.prototype;
        f.prototype.constructor = this.c;
        var obj = new f();
        this.c.apply(obj, arguments);
        return obj;
    },
    
    /**
     * Returns the default constructor function for new classes. You might want to override this in derived meta classes
     * Default calls initialize on a new object upon construction.
     * The class object will stringify to it's name
     * @function
     * @name defaultClassFunctionBody
     * @memberof Joose.Class
     */
    /** @ignore */
    defaultClassFunctionBody: function () {
        var f = function () {
            this.initialize.apply(this, arguments);
        };
        joose.addToString(f, function () {
            return this.meta.className()
        })
        return f;
    },
    
    /**
     * Adds a toString method to a class
     * The default toString method will call the method stringify if available.
     * This make overriding stringification easier because toString cannot
     * be reliably overriden in some JS implementations.
     * @function
     * @name addToString
     * @memberof Joose.Class
     */
    /** @ignore */
    addToString: function () {
        this.addMethod("toString", function () {
            if(this.stringify) {
                return this.stringify()
            }
            return "a "+ this.meta.className()
        })
    },
    
    /**
     * Adds the method returned by the initializer method to the class
     * @function
     * @name addInitializer
     * @memberof Joose.Class
     */
    /** @ignore */
    addInitializer: function () {
        if(!this.c.prototype.initialize) {
            this.addMethod("initialize", this.initializer())
        }
    },
    
    /**
     * Adds a toString method to a class
     * @function
     * @name initializer
     * @memberof Joose.Class
     */
    /** @ignore */
    initializer: function () {
        return function initialize (paras) {
            var me = this;
            if(this.meta.isAbstract) {
                var name = this.meta.className();
                throw ""+name+" is an abstract class and may not instantiated."
            }
            var attributes = this.meta.getAttributes();
            for(var i in attributes) {
                if(attributes.hasOwnProperty(i)) {
                    var attr = attributes[i];
                    attr.doInitialization(me, paras);
                }
            }
        }
    },
    
    dieIfString: function (thing) {
        if(Joose.S.isString(thing)) {
            throw new TypeError("Parameter must not be a string.")
        }
    },
    
    addRole: function (roleClass) {
        this.dieIfString(roleClass);
        var c = this.getClassObject();
        if(roleClass.meta.apply(c)) {
            this.roles.push(roleClass);
            this.myRoles.push(roleClass);
        }
        
    },
    
    getClassObject: function () {
        return this.c
    },
    
    classNameToClassObject: function (className) {
        var top    = joose.top;
        var parts  = className.split(".");
        var object = top;
        for(var i = 0; i < parts.length; i++) {
            var part = parts[i];
            object   = object[part];
            if(!object) {
                throw "Unable to find class "+className
            }
        }
        return object
    },
    
    addNonJooseSuperClass: function (name, object) {
        
        var pseudoMeta     = new Joose.MetaClassBootstrap();
        pseudoMeta.builder = Joose.MetaClassBootstrap;
        var pseudoClass    = pseudoMeta.createClass(name)
        
        Joose.O.each(object, function(value, name) {
            if(typeof(value) == "function") {
                pseudoClass.meta.addMethod(name, value)
            } else {
                pseudoClass.meta.addAttribute(name, {init: value})
            }
        })
        
        this.addSuperClass(pseudoClass);
    },
    
    addSuperClass:    function (classObject) {
        this.dieIfString(classObject);
        var me    = this;
        
        //this._fixMetaclassIncompatability(classObject)
        
        // Methods
        var names = classObject.meta.getMethodNames();
        for(var i = 0; i < names.length; i++) {
            var name = names[i]
            
            var m = classObject.meta.getMethodObject(name)
            if(m) {
                var method = m.copy();
                method.setIsFromSuperClass(true);
                me.addMethodObject(method)
            }
            m = classObject.meta.getClassMethodObject(name)
            if(m) {
                var method = m.copy();
                method.setIsFromSuperClass(true);
                me.addMethodObject(method)
            }
        } 
        
        // Attributes
        Joose.O.eachSafe(classObject.meta.attributes, function (attr, name) {
            me.addAttribute(name, attr.getProps())
        })
        
        // Roles
        var roles = classObject.meta.roles
        for(var i = 0; i < roles.length; i++) {
            var role = roles[i]
            me.roles.push(role)
        }
        
        this.parentClasses.unshift(classObject)
    },
    
    _fixMetaclassIncompatability: function (superClass) {
        
        var superMeta     = superClass.meta;
        var superMetaName = superMeta.meta.className();
        
        if(
          superMetaName == "Joose.Class"     ||
          superMetaName == "Joose.MetaClass" || 
          superMetaName == "Joose.MetaClassBootstrap") {
            return
        }
        
        // we are compatible
        if(this.meta.meta.isa(superMeta)) {
            return
        }
        
        // fix this into becoming a superMeta
        var patched = superMeta.meta.instantiate(this);
        
        for(var i in patched) {
            this[i] = patched[i]
        }
    },
    
    isa:            function (classObject) {
        this.dieIfString(classObject);
        var name = classObject.meta.className()
        // Same type
        if(this.className() == name) {
            return true
        }
        // Look up into parent classes
        for(var i = 0; i < this.parentClasses.length; i++) {
            var parent = this.parentClasses[i].meta
            if(parent.className() == name) {
                return true
            }
            if(parent.isa(classObject)) {
                return true
            }
        }
        return false
    },
    
    wrapMethod:  function (name, wrappingStyle, func, notPresentCB) {
        
        var orig = this.getMethodObject(name);
        if(orig) {
            this.addMethodObject( orig[wrappingStyle](func) )
        } else {
            if(notPresentCB) {
                notPresentCB()
            } else {
                throw new Error("Unable to apply "+wrappingStyle+" method modifier because method "+name+" does not exist");
            }
        }
    },
    
    dispatch:        function (name) {
        return this.getMethodObject(name).asFunction()
    },
    
    hasMethod:         function (name) {
        return this.methods[name] != null || this.classMethods[name] != null
    },
    
    addMethod:         function (name, func, props) {
        var m = new Joose.Method(name, func, props);
        
        this.addMethodObject(m)
    },
    
    addClassMethod:         function (name, func, props) {
        var m = new Joose.ClassMethod(name, func, props);
        
        this.addMethodObject(m)
    },
    
    addMethodObject:         function (method) {
        var m              = method;
        var name           = m.getName();
        
        if(!this.methods[name] && !this.classMethods[name]) {
            this.methodNames.push(name);
        }
        if(m.isClassMethod()) {
            this.classMethods[name] = m;
        } else {
            this.methods[name] = m;
        }
        
        method.addToClass(this.c)
    },
    
    attributeMetaclass: function () {
        return Joose.Attribute
    },
    
    addAttribute:     function (name, props) {
        
        var metaclass = this.attributeMetaclass();
        
        if(props && props.metaclass) {
            metaclass = props.metaclass
        }
        
        var at = new metaclass(name, props);
        
        at.apply(this.c)
    },
    
    getAttributes: function () {
        return this.attributes
    },
    
    getAttribute: function (name) {
        return this.attributes[name]
    },
    
    setAttribute: function (name, attributeObject) {
        return this.attributes[name] = attributeObject
    },
    
    getMethodObject: function (name) {
        return this.methods[name]
    },
    
    getClassMethodObject: function (name) {
        return this.classMethods[name]
    },
    
    getAttributeNames: function () {
        return this.attributeNames;
    },
    
    getInstanceMethods: function () {
        var a = [];
        Joose.O.eachSafe(this.methods, function (m) {
            a.push(m)
        })
        return a
    },
    
    getClassMethods: function () {
        var a = [];
        Joose.O.eachSafe(this.classMethods, function (m) {
            a.push(m)
        })
        return a
    },

    getSuperClasses:    function () {
        return this.parentClasses;
    },
    
    getSuperClass:    function () {
        return this.parentClasses[0];
    },
    
    getRoles:    function () {
        return this.roles;
    },
    
    getMethodNames:    function () {
        return this.methodNames;
    },
    
    makeAnonSubclass: function () {
        var c    = this.createClass(this.className()+"__anon__"+joose.anonymouseClassCounter++);
        c.meta.addSuperClass(this.getClassObject());
        
        return c;
    },
    
    addDetacher: function () {
        this.addMethod("detach", function detach () {
            var meta = this.meta;
            
            if(meta.isDetached) {
                return // no reason to do it again
            } 
            
            var c    = meta.makeAnonSubclass()
            
            c.meta.isDetached = true;
            
            // appy the role to the anonymous class
            // swap meta class of object with new instance
            this.meta      = c.meta;
            // swap __proto__ chain of object to its new class
            // unfortunately this is not available in IE :(
            // object.__proto__ = c.prototype
 
            this.constructor = c;
            
            var proto;
            
            // Workaround for IE and opera to enable prototype extention via the meta class (by making them identical :)
            // This however makes Role.unapply impossible
            if(!this.__proto__) {
                proto = this
            } else {
                proto   = {};
                Joose.copyObject(this, proto)
            }
            
            
            c.prototype    = proto;
            this.__proto__ = c.prototype
            return
        })
    },
    
    /**
     * Throws an exception if the class does not implement all methods required by it's roles
     * @function
     * @name validateClass
     * @memberof Joose.Class
     */
    validateClass: function () {
        var c  = this.getClassObject();
        var me = this;
        
        // Test whether all rows are fully implemented.
        var throwException = true;
        Joose.A.each(this.roles, function(role) {
              role.meta.isImplementedBy(c, throwException)
        })
    },
    
            /**
     * Returns true if the class implements the method 
     * @function
     * @name can
     * @param {string} methodName The method
     * @memberof Joose.Class
     */    
    can: function (methodName) {
        var method = this.methods[methodName];
        if(!method) {
            return false
        }
        return true
    },
    
    classCan: function (methodName) {
        var method = this.classMethods[methodName];
        if(!method) {
            return false
        }
        return true
    },
    
    
    /**
     * Returns true if the class implements a Role
     * @function
     * @name does
     * @param {Joose.Class} methodName The class object
     * @memberof Joose.Class
     */    
    does: function (roleObject) {
        
        for(var i = 0; i < this.roles.length; i++) {
            if(roleObject === this.roles[i]) {
                return true
            }
        }
        
        // dive into roles to find roles implemented by my roles
        for(var i = 0; i < this.roles.length; i++) {
            if(this.roles[i].meta.does(roleObject)) {
                return true
            }
        }
        
        return false
        // return classObject.meta.implementsMyMethods(this.getClassObject())
    },
    
    /**
     * Returns true if the given class implements all methods of the class 
     * @function
     * @name does
     * @param {Joose.Class} methodName The class object
     * @memberof Joose.Class
     */    
    implementsMyMethods: function (classObject) {
        var complete = true
        // FIXME buggy if class methods are involved. Should roles have class methods?
        Joose.A.each(this.getMethodNames(), function (value) {
            var found = classObject.meta.can(value)
            if(!found) {
                complete = false
            }
        })
        return complete
    },
    
    // Class builders:

    /**
     * Tells a role that the method name must be implemented by all classes that implement the role
     * @function
     * @param methodName {string} Name of the required method name
     * @name requires
     * @memberof Joose.Builder
     */    
    /** @ignore */
    handleProprequires:    function (methodName) {
        var me = this;
        if(!this.meta.isa(Joose.Role)) {
            throw("Keyword 'requires' only available classes with a meta class of type Joose.Role")
        }
        if(methodName instanceof Array) {
            Joose.A.each(methodName, function (name) {
                me.addRequirement(name)
            })
        } else {
            me.addRequirement(methodName)
        }
    },
    
    handlePropisAbstract: function (bool) {
        this.isAbstract = bool
    },
    
    
    /**
     * Class builder method
     * Defines the super class of the class
     * @function
     * @param classObject {Joose.Class} The super class
     * @name isa
     * @memberof Joose.Builder
     */    
    /** @ignore */
    handlePropisa:    function (classObject) {
        this.addSuperClass(classObject)
    },
    /**
     * Class builder method
     * Defines a role for the class
     * @function
     * @param classObject {Joose.Role} The role
     * @name does
     * @memberof Joose.Builder
     */    
    /** @ignore */
    handlePropdoes:    function (role) {
        var me = this;
        if(role instanceof Array) {
            Joose.A.each(role, function (aRole) {
                me.addRole(aRole)
            })
        } else {
            me.addRole(role)
        }
        
    },
    
    /**
     * Class builder method
     * Defines attributes for the class
     * @function
     * @param classObject {object} Maps attribute names to properties (See Joose.Attribute)
     * @name has
     * @memberof Joose.Builder
     */    
    /** @ignore */
    handleProphas:    function (map) {
        var me = this;
        if(typeof map == "string") {
            var name  = arguments[0];
            var props = arguments[1];
            me.addAttribute(name, props)
        } else { // name is a map
            Joose.O.eachSafe(map, function (props, name) {
                me.addAttribute(name, props)
            })
        }
    },
    
    /**
     * @ignore
     */    
    handlePropmethod: function (name, func, props) {
        this.addMethod(name, func, props)
    },
    
    /**
     * Class builder method
     * Defines methods for the class
     * @function
     * @param classObject {object} Maps method names to function bodies
     * @name methods
     * @memberof Joose.Builder
     */    
    /** @ignore */
    handlePropmethods: function (map) {
        var me = this
        Joose.O.eachSafe(map, function (func, name) {
            me.addMethod(name, func)
        })
    },
    
    /**
     * Class builder method
     * Defines class methods for the class
     * @function
     * @param classObject {object} Maps class method names to function bodies
     * @name classMethods
     * @memberof Joose.Builder
     */    
    /** @ignore */
    handlePropclassMethods: function (map) {
        var me = this;
        Joose.O.eachSafe(map, function (func, name2) {
            me.addMethodObject(new Joose.ClassMethod(name2, func))
        })
    },
    
    /**
     * Class builder method
     * Defines workers for the class (The class must have the meta class Joose.Gears)
     * @function
     * @param classObject {object} Maps method names to function bodies
     * @name workers
     * @memberof Joose.Builder
     */    
    /** @ignore */
    handlePropworkers: function (map) {
        var me = this;
        Joose.O.eachSafe(map, function (func, name) {
            me.addWorker(name, func)
        })
    },
    
    /**
     * Class builder method
     * Defines before method modifieres for the class.
     * The defined method modifiers will be called before the method of the super class.
     * The return value of the method modifier will be ignored
     * @function
     * @param classObject {object} Maps method names to function bodies
     * @name before
     * @memberof Joose.Builder
     */    
    /** @ignore */
    handlePropbefore: function(map) {
        var me = this
        Joose.O.eachSafe(map, function (func, name) {
            me.wrapMethod(name, "before", func);
        }) 
    },
    
    /**
     * Class builder method
     * Defines after method modifieres for the class.
     * The defined method modifiers will be called after the method of the super class.
     * The return value of the method modifier will be ignored
     * @function
     * @param classObject {object} Maps method names to function bodies
     * @name after
     * @memberof Joose.Builder
     */    
    /** @ignore */
    handlePropafter: function(map) {
        var me = this
        Joose.O.eachSafe(map, function (func, name) {
            me.wrapMethod(name, "after", func);
        }) 
    },
    
    /**
     * Class builder method
     * Defines around method modifieres for the class.
     * The defined method modifiers will be called instead of the method of the super class.
     * The orginial function is passed as an initial parameter to the new function
     * @function
     * @param classObject {object} Maps method names to function bodies
     * @name around
     * @memberof Joose.Builder
     */    
    /** @ignore */
    handleProparound: function(map) {
        var me = this
        Joose.O.eachSafe(map, function (func, name) {
            me.wrapMethod(name, "around", func);
        }) 
    },
    
    /**
     * Class builder method
     * Defines override method modifieres for the class.
     * The defined method modifiers will be called instead the method of the super class.
     * You can call the method of the super class by calling this.SUPER(para1, para2)
     * @function
     * @param classObject {object} Maps method names to function bodies
     * @name override
     * @memberof Joose.Builder
     */    
    /** @ignore */
    handlePropoverride: function(map) {
        var me = this
        Joose.O.eachSafe(map, function (func, name) {
            me.wrapMethod(name, "override", func);
        }) 
    },
    
    /**
     * Class builder method
     * Defines augment method modifieres for the class.
     * These method modifiers will be called in "most super first" order
     * The methods may call this.INNER() to call the augement method in it's sup class.
     * @function
     * @param classObject {object} Maps method names to function bodies
     * @name augment
     * @memberof Joose.Builder
     */    
    /** @ignore */
    handlePropaugment: function(map) {
        var me = this
        Joose.O.eachSafe(map, function (func, name) {
            me.wrapMethod(name, "augment", func, function () {
                me.addMethod(name, func)
            });
        }) 
    },
    
    /**
     * @ignore
     */    
    handlePropdecorates: function(map) {
        var me = this
        Joose.O.eachSafe(map, function (classObject, attributeName) {
            me.decorate(classObject, attributeName)
        }) 
    }
};

// See /web/20110721091305/http://code.google.com/p/joose-js/wiki/JooseAttribute
Joose.Attribute = function (name, props) {
    this.initialize(name, props)
}

Joose.Attribute.prototype = {
    
    _name:  null,
    _props: null,
    
    getName:    function () { return this._name },
    getProps:    function () { return this._props },
    
    initialize: function (name, props) {
        this._name  = name;
        this.setProps(props);
    },
    
    setProps: function (props) {
        if(props) {
            this._props = props
        } else {
            this._props = {};
        }
    },
    
    getIsa: function () {
        var props = this.getProps();
        if(props.isa) {
            if(!props.isa.meta) {
                return props.isa()
            }
            return props.isa
        }
        return
    },
    
    addSetter: function (classObject) {
        var meta  = classObject.meta;
        var name  = this.getName();
        var props = this.getProps();
        
        var isa   = this.getIsa();

        var func;
        if(isa) {
        	if(!isa.meta) {
        		throw new Error("Isa declarations in attribute declarations must be Joose classes, roles or type constraints")
        	}
        	
        	var isRole  = false;
        	var isType  = false;
        	// We need to check whether Joose.Role and Joose.TypeContraint 
        	// are there yet, because they might not have been compiled yet
        	if(Joose.Role && isa.meta.meta.isa(Joose.Role)) {
        		isRole  = true;
        	} 
        	else if(Joose.TypeConstraint && isa.meta.isa(Joose.TypeConstraint)) {
        		isType  = true;
        	}
        	
        	// This setter is used if the attribute is constrained with an isa property in the attribute initializer
        	// If the isa refers to a class, then the new value must be an instance of that class.
        	// If the isa refers to a role,  then the new value must implement that role.
        	// If the isa refers to a type constraint, then the value must match that type contraint
        	// ...and if the coerce property is set, we try to coerce the new value into the type
        	// Throws an exception if the new value does not match the isa property.
        	// If errorHandler is given, it will be executed in case of an error with parameters (Exception, isa-Contraint)
            func = function setterWithIsaCheck (val, errorHandler) {
            	var value = val
            	try {
                	if ( props.nullable === true && value == undefined) {
                	    // Don't do anything here :)
                	} else if ( isType ) {
                	    var newvalue = null;
                	    if( props.coerce ) {
                	        newvalue = isa.coerce(value);
                	    }
                	    if ( newvalue == null && props.nullable !== true) {
                	        isa.validate(value);
                	    } else {
                	    	value = newvalue;
                	    }
                	} else {
                	    if(!value || !value.meta) {
                	        throw new ReferenceError("The attribute "+name+" only accepts values that have a meta object.")
                	    }
                	    var typeCheck = isRole ? value.meta.does(isa) : value.meta.isa(isa);
                	    if( ! typeCheck ) {
                	        throw new ReferenceError("The attribute "+name+" only accepts values that are objects of type "+isa.meta.className()+".")
                	    }
                	}
            	} catch (e) {
            		if(errorHandler) {
            			errorHandler.call(this, e, isa)
            		} else {
            			throw e
            		}
            	};
                this[name] = value
                return this;
            }
        } else {
            func = function setter (value) {
                this[name] = value
                return this;
            }
        }
        meta.addMethod(this.setterName(), func);
    },
    
    
    addGetter: function (classObject) {
        var meta  = classObject.meta;
        var name  = this.getName();
        var props = this.getProps();
        
        var func  = function getter () {
            return this[name]
        }
        
        var init  = props.init;
        
        if(props.lazy) {
            func = function lazyGetter () {
                var val = this[name];
                if(typeof val == "function" && val === init) {
                    this[name] = val.apply(this)
                }
                return this[name]
            }
        }
        
        meta.addMethod(this.getterName(), func);
    },
    
    initializerName: function () {
        return this.toPublicName()
    },
    
    getterName: function () {
        if(this.__getterNameCache) { // Cache the getterName (very busy function)
            return this.__getterNameCache
        }
        this.__getterNameCache = "get"+Joose.S.uppercaseFirst(this.toPublicName())
        return this.__getterNameCache;
    },
    
    setterName: function () {
        if(this.__setterNameCache) { // Cache the setterName (very busy function)
            return this.__setterNameCache
        }
        this.__setterNameCache = "set"+Joose.S.uppercaseFirst(this.toPublicName())
        return this.__setterNameCache;
    },
    
    isPrivate: function () {
        return this.getName().charAt(0) == "_"
    },
    
    toPublicName: function () {
        
        if(this.__publicNameCache) { // Cache the publicName (very busy function)
            return this.__publicNameCache
        }
        
        var name = this.getName();
        if(this.isPrivate()) {
            this.__publicNameCache = name.substr(1)
            return this.__publicNameCache;
        }
        this.__publicNameCache = name
        return this.__publicNameCache
    },
    
    handleIs: function (classObject) {
        var meta  = classObject.meta;
        var name  = this.getName();
        var props = this.getProps();
        
        var is    = props.is;

        if(is == "rw" || is == "ro") {
            this.addGetter(classObject);
        }
        if(is == "rw") {
            this.addSetter(classObject)
        }
    },
    
    handleInit: function (classObject) {
        var props = this.getProps();
        var name  = this.getName();
        
        classObject.prototype[name]     = null;
        if(typeof props.init != "undefined") {
            var val = props.init;
            var type = typeof val;

            classObject.prototype[name] = val;
        }
    },
    
    handleProps: function (classObject) {
        this.handleIs(classObject);
        this.handleInit(classObject)
    },
    
    apply: function (classObject) {
        
        var meta  = classObject.meta;
        var name  = this.getName();
        
        this.handleProps(classObject)
        
        meta.attributeNames.push(name)
        
        meta.setAttribute(name, this)
        meta.attributes[name] = this;
    }
    
    
}

// See /web/20110721091305/http://code.google.com/p/joose-js/wiki/JooseMethod
Joose.Method = function (name, func, props) {
    this.initialize(name, func, props)
}

Joose.Method.prototype = {
    
    _name: null,
    _body: null,
    _props: null,
    _isFromSuperClass: false,
    
    getName:    function () { return this._name },
    getBody:    function () { return this._body },
    getProps:   function () { return this._props },
    
    isFromSuperClass: function () {
        return this._isFromSuperClass
    },
    
    setIsFromSuperClass: function (bool) {
        this._isFromSuperClass = bool
    },
    
    copy: function () {
        // Hardcode class name because at this point this.meta.instantiate might not work yet
        // this is later overridden in the file Joose/Method.js
        return new Joose.Method(this.getName(), this.getBody(), this.getProps())
    },
    
    initialize: function (name, func, props) {
        this._name  = name;
        this._body  = func;
        this._props = props;
        
        func.name   = name
    
        func.meta   = this
    },
    
    isClassMethod: function () { return false },
    
    apply:    function (thisObject, args) {
        return this._body.apply(thisObject, args)
    },
    
    addToClass: function (c) {
        c.prototype[this.getName()] = this.asFunction()
    },
    
    // direct call
    asFunction:    function () {
        return this._body
    }
}
Joose.bootstrap()


// ##########################
// File: Joose/Builder.js
// ##########################
// Could be refactored to a Joose.Class (by manually building the class)

/**
 * Assorted tools to build a class
 * 
 * The functions Class(), Module() and joosify() are global. All other methods
 * may be used inside Class definitons like this:
 * 
 * <pre>
 * Module("com.test.me", function () {
 *   Class("MyClass", {
 *     isa: SuperClass,
 *     methods: {
 *       hello: function () { alert('world') }
 *     }
 *   })
 * })
 * </pre>
 * @constructor
 */



Joose.Builder = function () {
    /** @ignore */
    this.globalize = function () {
        Joose.O.each(Joose.Builder.Globals, function (func, name) {
            var globalName = "Joose"+name
            if(typeof joose.top[name] == "undefined") {
                joose.top[name] = func
            }
            
            joose.top[globalName] = func
        });
    }
}

/** @ignore */
Joose.Builder.Globals = {
    /**
     * Global function that creates or extends a module
     * @function
     * @param name {string} Name of the module
     * @param functionThatCreatesClassesAndRoles {function} Pass a function reference that calls Class(...) as often as you want. The created classes will be put into the module
     * @name Module
     */    
    /** @ignore */
    Module: function (name, functionThatCreatesClassesAndRoles) {
        return Joose.Module.setup(name, functionThatCreatesClassesAndRoles)
    },
    
    Role: function (name, props) {
        if(!props.meta) {
            props.meta = Joose.Role;
        }
        return JooseClass(name, props)
    },
    
    Prototype: function (name, props) {
        if(!props.meta) {
            props.meta = Joose.Prototype;
        }
        return JooseClass(name, props);
    },
    
    /**
     * Global function that creates a class (If the class already exists it will be extended)
     * @function
     * @param name {string} Name of the the class
     * @param props {object} Declaration if the class. The object keys are used as builder methods. The values are passed as arguments to the builder methods.
     * @name Class
     */    
    /** @ignore */
    Class:    function (name, props) {
        
        var c = null;
        
        if(name) {
            var className  = name;
            if(joose.currentModule) {
                className  = joose.currentModule.getName() + "." + name
            }
            var root       = joose.top;
            var parts      = className.split(".")
        
            for(var i = 0; i < parts.length; i++) {
                root = root[parts[i]]
            }
            c = root;
        }

        if(c == null) {
            
            var metaClass;
            
            /* Use the custom meta class if provided */
            if(props && props.meta) {
                metaClass = props.meta
                delete props.meta
            }
            /* Otherwise use the meta class of the parent class (If there is one)
             * If the parent class is Joose.Class, we don't change the meta class but use the default
             * because that Joose.Class's meta class is only needed for bootstrapping
             * purposes. */
            else if(props && props.isa && props.isa != Joose.Class) {
                metaClass = props.isa.meta.builder
                //alert(name + metaClass + props.isa.meta)
            }
            /* Default meta class is Joose.Class */
            else {
                metaClass   = Joose.Class;
            }    
            
            var aClass      = new metaClass();
            
            aClass.builder  = metaClass;

            var c           = aClass.createClass(name, null, joose.currentModule)
            
            c.meta.builder  = metaClass
            
            var className   = c.meta.className()
            
            if(name && className) {
                var root = joose.top;
                var n = new String(className);
                var parts = n.split(".");
                for(var i = 0; i < parts.length - 1; i++) {
                    if(root[parts[i]] == null) {
                        root[parts[i]] = {};
                    }
                    root = root[parts[i]];
                }
                root[parts[parts.length - 1]] = c
            }
            
        }
        
        c.meta.initializeFromProps(props)
        
        return c
    },
    
    Type: function (name, props) {
        var t = Joose.TypeConstraint.newFromTypeBuilder(name, props);
        
        var m = joose.currentModule
        
        if(!m) {
            JooseModule("TYPE")
            m = TYPE.meta;
        }
        
        m.addElement(t)
        m.getContainer()[name] = t;
        return t
    },
    
    /**
     * Global function to turn a regular JavaScript constructor into a Joose.Class
     * @function
     * @param name {string} Name of the class
     * @param props {function} The constructor
     * @name joosify
     */    
    /** @ignore */
    joosify: function (standardClassName, standardClassObject) {
        var c         = standardClassObject;
        var metaClass = new Joose.Class();
        metaClass.builder = Joose.Class;
        
        c.toString = function () { return this.meta.className() }
        c             = metaClass.createClass(standardClassName, c)
    
        var meta = c.meta;
    
        for(var name in standardClassObject.prototype) {
            if(name == "meta") {
                continue
            }
            var value = standardClassObject.prototype[name]
            if(typeof(value) == "function") {
                meta.addMethod(name, value)
            } else {
                var props = {};
                if(typeof(value) != "undefined") {
                    props.init = value
                }
                meta.addAttribute(name, props)
            }
        }
        
        return c
    },
    
    /** @ignore */
    rw: "rw",
    /** @ignore */
    ro: "ro"
};

joose.init();
// ##########################
// File: Joose/Class.js
// ##########################


Joose.bootstrap2();
// ##########################
// File: Joose/Method.js
// ##########################
/*
 * A class for methods
 * Originally defined in Joose.js
 * 
 * See /web/20110721091305/http://code.google.com/p/joose-js/wiki/JooseMethod
 */

(function (Class) {

Class("Joose.Method", {
    methods: {
        
        copy: function () {
            return this.meta.instantiate(this.getName(), this.getBody(), this.getProps())
        },
        
        // creates a new method object with the same name
        _makeWrapped: function (func) {
            return this.meta.instantiate(this.getName(), func); // Should there be , this.getProps() ???
        },
        
        around: function (func) {
            var orig = this.getBody();
            return this._makeWrapped(function aroundWrapper () {
                var me = this;
                var bound = function () { return orig.apply(me, arguments) }
                return func.apply(this, Joose.A.concat([bound], arguments))
            })            
        },
        before: function (func) {
            var orig = this.getBody();
            return this._makeWrapped(function beforeWrapper () {
                func.apply(this, arguments)
                return orig.apply(this, arguments);
            })        
        },
        after: function (func) {
            var orig = this.getBody();
            return this._makeWrapped(function afterWrapper () {
                var ret = orig.apply(this, arguments);
                func.apply(this, arguments);
                return ret
            })
        },
        
        override: function (func) {
            var orig = this.getBody();
            return this._makeWrapped(function overrideWrapper () {
                var me      = this;
                var bound   = function () { return orig.apply(me, arguments) }
                var before  = this.SUPER;
                this.SUPER  = bound;
                var ret     = func.apply(this, arguments);
                this.SUPER  = before;
                return ret
            })            
        },
        
        augment: function (func) {
            var orig = this.getBody();
            orig.source = orig.toString();
            return this._makeWrapped(function augmentWrapper () {
                var exe       = orig;
                var me        = this;
                var inner     = func
                inner.source  = inner.toString();
                if(!this.__INNER_STACK__) {
                    this.__INNER_STACK__ = [];
                };
                this.__INNER_STACK__.push(inner)
                var before    = this.INNER;
                this.INNER    = function () {return  me.__INNER_STACK__.pop().apply(me, arguments) };
                var ret       = orig.apply(this, arguments);
                this.INNER    = before;
                return ret
            })
        }
    }
})

})(JooseClass);

// ##########################
// File: Joose/ClassMethod.js
// ##########################
(function (Class) {
    
Class("Joose.ClassMethod", {
    isa: Joose.Method,
    methods: {
        isClassMethod: function () { return true },
        addToClass: function (c) {
            c[this.getName()] = this.asFunction()
        },
        
        copy: function () {
            return new Joose.ClassMethod(this.getName(), this.getBody(), this.getProps())
        }
    }
})

})(JooseClass);

// ##########################
// File: Joose/Attribute.js
// ##########################
/*
 * This handles the following attribute properties
 *  * init with function value in non-lazy initialization
 *  * required attributes in initializaion
 *  * handles for auto-decoration
 *  * predicate for attribute availability checks
 * 
 * 
 * See /web/20110721091305/http://code.google.com/p/joose-js/wiki/JooseAttribute
 */

(function (Class) {
Class("Joose.Attribute", {
    after: {
        handleProps: function (classObject) {
            this.handleHandles(classObject);
            this.handlePredicate(classObject);
        }
    },
    methods: {
        
        isPersistent: function () {
            var props = this.getProps()
            if(props.persistent == false) {
                return false
            }
            return true
        },
        
        doInitialization: function (object, paras) {
            var  name  = this.initializerName();
            var _name  = this.getName();
            var value;
            var isSet  = false;
            if(typeof paras != "undefined" && typeof paras[name] != "undefined") {
                value  = paras[name];
                isSet  = true;
            } else {
                var props = this.getProps();
                
                var init  = props.init;
                
                if(typeof init == "function" && !props.lazy) {
                    // if init is not a function, we have put it in the prototype, so it is already here
                    value = init.call(object)
                    isSet = true
                } else {
                    // only enforce required property if init is not run
                    if(props.required) {
                        throw "Required initialization parameter missing: "+name + "(While initializing "+object+")"
                    }
                }
            }
            if(isSet) {
                var setterName = this.setterName();
                if(object.meta.can(setterName)) { // use setter if available
                    object[setterName](value)
                } else { // direct attribute access
                    object[_name] = value
                }
            }
        },
        
        handleHandles: function (classObject) {
            var meta  = classObject.meta;
            var name  = this.getName();
            var props = this.getProps();
            
            var handles = props.handles;
            var isa     = props.isa
            
            if(handles) {
                if(handles == "*") {
                    if(!isa) {
                        throw "I need an isa property in order to handle a class"
                    }
                    
                    // receives the name and should return a closure
                    var optionalHandlerMaker = props.handleWith;
                    
                    meta.decorate(isa, name, optionalHandlerMaker)
                } 
                else {
                    throw "Unsupported value for handles: "+handles
                }
                
            }
        },
        
        handlePredicate: function (classObject) {
            var meta  = classObject.meta;
            var name  = this.getName();
            var props = this.getProps();
            
            var predicate = props.predicate;
            
            var getter    = this.getterName();
            
            if(predicate) {
                meta.addMethod(predicate, function () {
                    var val = this[getter]();
                    return val ? true : false
                })
            }
        }
    }
})
})(JooseClass);

// ##########################
// File: Joose/Role.js
// ##########################

/*
 * An Implementation of Traits
 * see /web/20110721091305/http://www.iam.unibe.ch/~scg/cgi-bin/scgbib.cgi?query=nathanael+traits+composable+units+ecoop
 * 
 * Current Composition rules:
 * - At compile time we override existing (at the time of rule application) methods
 * - At runtime we dont
 */

(function (Class) {

Class("Joose.Role", {
    isa: Joose.Class,
    has: ["requiresMethodNames", "methodModifiers", "metaRoles"],
    methods: {
        
        // Add a method modifier that will be applied to classes implementing this role.
        wrapMethod: function (name, wrappingStyle, func, notPresentCB) {
            // queue arguments given to this function for later application to actual class
            this.methodModifiers.push(arguments)
            var test = this.methodModifiers
        },
        
        requiresMethod: function (methodName) {
            var bool = false;
            Joose.A.each(this.requiresMethodNames, function (name) {
                if(methodName == name) {
                    bool = true
                }
            })
            
            return bool
        },
        
        addInitializer: Joose.emptyFunction,
        
        // Roles can not be instantiated
        defaultClassFunctionBody: function () {
            var f = function () {
                throw new Error("Roles may not be instantiated.")
            };
            joose.addToString(f, function () { return this.meta.className() })
            return f
        },
        
        // Roles can not be instantiated
        addSuperClass: function () {
            throw new Error("Roles may not inherit from a super class.")
        },
        
        initialize: function () {
            this._name               = "Joose.Role"
            this.requiresMethodNames = [];
            this.methodModifiers     = [];
        },
        
        // Class implementing this role must implement a method named methodName
        addRequirement: function (methodName) {
            this.requiresMethodNames.push(methodName)
        },
        
        // Experimental method to unapply classes from roles.
        // Only works on roles that were applied at runtime
        // Currently does not work in IE (depends on __proto__)
        unapply: function (object) {
            if(!joose.isInstance(object)) {
                throw new Error("You way only remove roles from instances.")
            }
            if(!object.meta.isDetached) {
                throw new Error("You may only remove roles that were applied at runtime")
            }
            
            var role  = this.getClassObject()
            
            var roles = object.meta.myRoles; // myRoles!!!
            var found = false;
            var otherRoles = [];
            for(var i = 0; i < roles.length; i++) {
                if(roles[i] === role) {
                    found = true;
                } else {
                    otherRoles.push(roles[i])
                }
            }
            if(!found) {
                throw new Error("The role "+this.className()+" was not applied to the object at runtime")
            }
            
            var superClass     = object.meta.getSuperClass();
            var c              = superClass.meta.makeAnonSubclass();
            
            
            // rebless object
            /*if(typeof(object.__proto__) != "undefined") {
                object.__proto__ = c.prototype                    
            } else {   // Workaround for IE: 
            */
            
            var test = new c()
            
            // add all roles except the one that we are removing
            for(var i = 0; i < otherRoles.length; i++) {
                var role = otherRoles[i]
                c.meta.addRole(role)
            }
            
            c.prototype        = test
            
            object.meta        = c.meta;
            object.constructor = c;
            object.__proto__   = test
        },
        
        addMethodToClass: function (method, classObject) {
            var name = method.getName()
            var cur;
            if(method.isClassMethod()) {
                cur = classObject.meta.getClassMethodObject(name)
            } else {
                cur = classObject.meta. getMethodObject(name)
            }
            // Methods from roles take precedence over methods from a super class
            if(!cur || cur.isFromSuperClass()) {
                classObject.meta.addMethodObject(method)
            }
        },
    
        apply: function (object) {
            
            // XXX ask in #moose whether this is correct
            // A Role should not be applied twice
            if(object.meta.does(this.getClassObject())) {
                return false
            }
            
            if(joose.isInstance(object)) {
                // Create an anonymous subclass ob object's class
                
                object.detach();
                object.meta.addRole(this.getClassObject());
                this.applyMethodModifiers(object);
                var throwException = true;
                this.isImplementedBy(object, throwException)
            } else {
                // object is actually a class
                var me    = this;
                var names = this.getMethodNames();
        
                //alert("Super"+me.name + " -> "+classObject.meta.name +"->" + names)
        
                Joose.A.each(names, function applyMethod (name) {
                    
                    var m = me.getMethodObject(name)
                    if(m) {
                        me.addMethodToClass(m, object)
                    }
                    
                    m = me.getClassMethodObject(name)
                    if(m) {
                        me.addMethodToClass(m, object)
                    }
                })
                

                // Meta roles are applied to the meta class of the class that implements us
                if(this.metaRoles) {
                    Joose.A.each(this.metaRoles, function applyMetaRole (role) {
                        role.meta.apply(object.meta)
                    })
                }
            }
            return true
        },
        
        // should be called by class builder after class has been initialized from props
        applyMethodModifiers: function (object) {
            
            // Apply method modifiers
            Joose.A.each(this.methodModifiers, function applyMethodModifier (paras) {
                object.meta.wrapMethod.apply(object.meta, paras)
            })
        },
        
        // Checks whether classObject (can also be any Joose object) implements this role. 
        // If second para is true, throws an exception when a method is missing.
        hasRequiredMethods: function (classObject, throwException) {
            var me       = this
            var complete = true
            Joose.A.each(this.requiresMethodNames, function (value) {
                var found = classObject.meta.can(value)
                if(!found) {
                    if(throwException) {
                         throw("Class "+classObject.meta.className()+" does not fully implement the role "+me.className()+". The method is "+value+" missing.")
                    }
                    complete = false
                    return
                }
            })
            return complete
        },
        
        // This is called by validateClass in Joose.Class.
        // This is not part of apply because apply might be called way before class construction is complete.
        isImplementedBy: function (classObject, throwException) {
        
            var complete = this.hasRequiredMethods(classObject, throwException);
            if(complete) {
                complete = this.implementsMyMethods(classObject);
            }
            return complete
        },
        
        // the metaRoles prop allows a role to apply roles to the meta class of the class using the role
        handlePropmetaRoles: function (arrayOfRoles) {
            this.metaRoles = arrayOfRoles;
        }
    }
})

Joose.Role.anonymousClassCounter = 0;

})(JooseClass);

// ##########################
// File: Joose/SimpleRequest.js
// ##########################
/**
 * Class to perform simple synchronous AJAX Requests used for component loading.
 * @name Joose.SimpleRequest
 * @class
 */

(function (Class) {

Class("Joose.SimpleRequest", {

    has: {_req: {}},
    methods: {
        initialize: function () {
            if (window.XMLHttpRequest) {
                this._req = new XMLHttpRequest();
            } else {
                this._req = new ActiveXObject("Microsoft.XMLHTTP");
            }
        },
        /**
         * Fetches text from an URL
         * @name getText
         * @param {string} url The URL
         * @function
         * @memberof Joose.SimpleRequest
         */
        getText: function (url) {
            this._req.open("GET", url, false);
            try {
                this._req.send(null);
                if (this._req.status == 200 || this._req.status == 0)
                    return this._req.responseText;
            } catch (e) {
                throw("File not found: " + url);
                return null;
            };

            throw("File not found: " + url);
            return null;
        }
    }
})
})(JooseClass);

// ##########################
// File: Joose/Gears.js
// ##########################
/**
 * Joose.Gears is a meta class for classes that want to delegate work to gears workers
 * @name Joose.Gears
 * @extends Joose.Class
 * @constructor
 */

(function (Class) {

Class("Joose.Gears", {
    isa: Joose.Class,
    has: {
        wp: {  },
        calls: { init: {} },
        callIndex: { init: 0 }
    },
    
    methods: {
        initialize: function () {
            JooseGearsInitializeGears() 
            if(this.canGears()) {
                this.wp = google.gears.factory.create('beta.workerpool');
                var me = this;
                this.wp.onmessage = function (a,b,message) {
                    me.handleGearsMessage(message)
                }
            }
        },
        handleGearsMessage: function (message) {
            var paras  = message.body
            var cbName = paras.to;
            var ret    = paras.ret;
            var object = this.calls[paras.index];
            if(object.meta.can(cbName)) {
                object[cbName].call(object, ret)
            }
            //delete this.calls[paras.index]
        },
        
        canGears: function () {
            return window.google && window.google.gears && window.google.gears.factory
        },
        
        /**
         * Adds a worker to the class
         * @function
         * @name addWorker
         * @param {string} Name of the worker
         * @param {function} Function body of the worker
         * @param {props} Optional properties for the created method (ignored)
         * @memberof Joose.Gears
         */    
        addWorker:         function (name, func, props) {
            
            var cbName  = "on"+Joose.S.uppercaseFirst(name)

            var ajaxRequestFunc = this.meta.getClassObject().ajaxRequest;
            
            // No gears, then work inline
            if(!this.canGears()) {
                var wrapped = function () {
                    var me = this;
                    var object = {
                        sendReturn:     function (ret, cbName) { if(me.meta.can(cbName)) me[cbName].call(me, ret) },
                        clientHasGears: function () { return false },
                        ajaxRequest:    ajaxRequestFunc
                    };
                    var ret = func.apply(object, arguments);
                    object.sendReturn(ret, cbName)
                }
                this.addMethod(name, wrapped, props)
                return
            }
            
            // OK, we have gears support
            
            var jsonUrl = this.can("jsonURL") ? this.c.jsonURL() : "json2.js";
            
            var json    = new Joose.SimpleRequest().getText(jsonUrl)
                
            var source  = 
              "var timer = google.gears.factory.create('beta.timer');\n"+ // always provide timer
              "function aClass () {}; aClass.prototype."+name+" = "+func.toString()+"\n\n"+
              "aClass.prototype.clientHasGears = function () { return true }\n"+
              "aClass.prototype.ajaxRequest = "+ajaxRequestFunc.toString()+"\n\n"+
              "var wp = google.gears.workerPool;\n" +
              "wp.onmessage = function (a,b,message) {\n"+
              
              "var paras = message.body;\n"+
              
              "var o = new aClass();\n"+
              
              "o.sendReturn = function (ret, cbName) { wp.sendMessage({ ret: ret, to: cbName, index: paras.index }, message.sender) } \n"+ 
              
              "var ret = o."+name+".apply(o, paras.args); if(!ret) ret = null; \n"+
              "o.sendReturn(ret, paras.cbName);"+
              "\n}\n\n";
              
        
            
            source += json
            
            var wp      = this.wp;
            
            var childId = wp.createWorker(source)
            
            var me      = this
                
            var wrapped = function () {
                var args = [];
                for(var i = 0; i < arguments.length; i++) {
                    args.push(arguments[i])
                }
                var message = { args: args, cbName: cbName, index: me.callIndex };
                wp.sendMessage(message, childId);
                me.calls[me.callIndex] = this
                me.callIndex++
                
            }
            this.addMethod(name, wrapped, props)

        }
    },
    
    classMethods: {
        // builds an environment for non gears platform where the regular window looks more like a gears worker
        // APIs implemented: Timer
        setupGearsCompat: function () {
            // setup gears timer api
            window.timer = {
                setTimeout:    function (func, time) { return window.setTimeout(func, time) },
                setInterval:   function (func, time) { return window.setInterval(func, time) },
                clearTimeout:  function (timer) { return window.clearTimeout(timer) },
                clearInterval: function (timer) { return window.clearInterval(timer) }
            };
        },
        
        clientHasGears: function () { //  XXX code dup with instance method
            return window.google && window.google.gears && window.google.gears.factory
        },
        
        // a simple AJAX request that uses gears if available
        ajaxRequest: function (method, url, data, callback, errorCallback) {
        
            var request
            if(this.clientHasGears()) {
                request = google.gears.factory.create('beta.httprequest');
            } else {
                request = window.ActiveXObject ? new ActiveXObject("Microsoft.XMLHTTP") : new XMLHttpRequest();
            }
            var dataString    = ""
            if(data) {
                for(var i in data) {
                    dataString += encodeURIComponent(i)+"="+encodeURIComponent(data[i])+"&"
                }
            }
            var theUrl = url;
            if(data && method == "GET") {
                theUrl += "?"+dataString
            }
            request.open(method, theUrl, true);
                
            request.onreadystatechange = function onreadystatechange () {
                if (request.readyState == 4) {
                    if(request.status >= 200 && request.status < 400) {
                        var res = request.responseText;
                        callback(res)
                    } else {
                        if(errorCallback) {
                            return errorCallback(request)
                        } else {
                            throw new Error("Error fetching url "+theUrl+". Response code: " + request.status + " Response text: "+request.responseText)
                        }
                    }
                }
            };
            if(data && method == "POST") {
                // FIXME determine page encoding instead of always using UTF8
                request.setRequestHeader("Content-Type", "application/x-www-form-urlencoded; charset=UTF-8"); 
                request.send(dataString)
            } else {
                dataString = ""
                request.send(dataString);
            }
        }
    }
})

})(JooseClass);

// Copyright 2007, Google Inc.
//
// Redistribution and use in source and binary forms, with or without
// modification, are permitted provided that the following conditions are met:
//
//  1. Redistributions of source code must retain the above copyright notice,
//     this list of conditions and the following disclaimer.
//  2. Redistributions in binary form must reproduce the above copyright notice,
//     this list of conditions and the following disclaimer in the documentation
//     and/or other materials provided with the distribution.
//  3. Neither the name of Google Inc. nor the names of its contributors may be
//     used to endorse or promote products derived from this software without
//     specific prior written permission.
//
// THIS SOFTWARE IS PROVIDED BY THE AUTHOR ``AS IS'' AND ANY EXPRESS OR IMPLIED
// WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
// MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO
// EVENT SHALL THE AUTHOR BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
// SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
// PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS;
// OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY,
// WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR
// OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF
// ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
//
// Sets up google.gears.*, which is *the only* supported way to access Gears.
//
// Circumvent this file at your own risk!
//
// In the future, Gears may automatically define google.gears.* without this
// file. Gears may use these objects to transparently fix bugs and compatibility
// issues. Applications that use the code below will continue to work seamlessly
// when that happens.

// Sorry Google for modifying this :) 
function JooseGearsInitializeGears() {
  // We are already defined. Hooray!
  if (window.google && google.gears) {
    return;
  }

  var factory = null;

  // Firefox
  if (typeof GearsFactory != 'undefined') {
    factory = new GearsFactory();
  } else {
    // IE
    try {
      factory = new ActiveXObject('Gears.Factory');
      // privateSetGlobalObject is only required and supported on WinCE.
      if (factory.getBuildInfo().indexOf('ie_mobile') != -1) {
        factory.privateSetGlobalObject(this);
      }
    } catch (e) {
      // Safari
      if (navigator.mimeTypes["application/x-googlegears"]) {
        factory = document.createElement("object");
        factory.style.display = "none";
        factory.width = 0;
        factory.height = 0;
        factory.type = "application/x-googlegears";
        document.documentElement.appendChild(factory);
      }
    }
  }

  // *Do not* define any objects if Gears is not installed. This mimics the
  // behavior of Gears defining the objects in the future.
  if (!factory) {
    return;
  }

  // Now set up the objects, being careful not to overwrite anything.
  //
  // Note: In Internet Explorer for Windows Mobile, you can't add properties to
  // the window object. However, global objects are automatically added as
  // properties of the window object in all browsers.
  if (!window.google) {
    google = {};
  }

  if (!google.gears) {
    google.gears = {factory: factory};
  }
}



// ##########################
// File: Joose/Storage.js
// ##########################


(function (Class, Role) {

Role("Joose.Storage", {
    
    methods: {
        // gets called by the JSON.stringify method
        toJSON: function () {
            // Evil global var TEMP_SEEN. See Joose.Storage.Unpacker.patchJSON
            var packed = this.pack(Joose.Storage.TEMP_SEEN)
            
            packed.toJSON = function () { return this }
            
            return packed;
        },
        
        // Generate an object identity (a unique integer for this object
        // This is cached in a property called __ID__
        // Override this in object representing values
        identity: function () {
            if(this.__ID__) {
                return this.__ID__
            } else {
                return this.__ID__ = Joose.Storage.OBJECT_COUNTER++
            }
        },
        
        pack: function (seen) {
            return this.meta.c.storageEngine().pack(this, seen)
        }
    },
    
    classMethods: {
        
        storageEngine: function () {
            return Joose.Storage.Engine
        },
        
        unpack: function (data) {
            return this.storageEngine().unpack(this, data)
        }
    }
    
})



Role("Joose.Storage.jsonpickle", {
    does: Joose.Storage,
    
    classMethods: {
        storageEngine: function () {
            return Joose.Storage.Engine.jsonpickle
        }
    }
})

Joose.Storage.OBJECT_COUNTER = 1;

// This storage engine is base on MooseX::Storage: /web/20110721091305/http://search.cpan.org/~nuffin/MooseX-Storage-0.14/lib/MooseX/Storage.pm
Class("Joose.Storage.Engine", {
    
    classMethods: {
        
        pack: function (object, seen) {
            
            
            if(seen) {
                var id  = object.identity()
                var obj = seen[id];
                if(obj) {
                    return {
                        __ID__: id
                    }
                }
            }
            
            if(object.meta.can("prepareStorage")) {
                object.prepareStorage()
            }
            
            if(seen) {
                seen[object.identity()] = true
            }
            
            var o  = {
                __CLASS__: this.packedClassName(object),
                __ID__:    object.identity()
            };
            
            var attrs      = object.meta.getAttributes();
            
            Joose.O.eachSafe(attrs, function packAttr (attr, name) {
                if(attr.isPersistent()) {
                    o[name]   = object[name];
                }
            })
  
            return o
        },
        
        unpack: function (classObject, data) {
            var meta      = classObject.meta
            var me        = meta.instantiate();
            var seenClass = false;
            Joose.O.eachSafe(data, function unpack (value,name) {
                if(name == "__CLASS__") {
                    var className = Joose.Storage.Unpacker.packedClassNameToJSClassName(value)
                    if(className != me.meta.className()) {
                        throw new Error("Storage data is of wrong type "+className+". I am "+me.meta.className()+".")
                    }
                    seenClass = true
                    return
                }
                me[name] = value
            })
            if(!seenClass) {
                throw new Error("Serialized data needs to include a __CLASS__ attribute.: "+data)
            }
            
            // Unpacked id may come from another global counter and thus must be discarded
            delete me.__ID__
            
            if(me.meta.can("finishUnpack")) {
                me.finishUnpack()
            }
            
            return me
        },
        
        packedClassName: function (object) {
            if(object.meta.can("packedClassName")) {
                return object.packedClassName();
            }
            var name   = object.meta.className();
            var parts  = name.split(".");
            return parts.join("::");
        }
    }
    
})

Class("Joose.Storage.Engine.jsonpickle", {
    
    classMethods: {
        
        pack: function (object, seen) {
            
            
            if(seen) {
                var id  = object.identity()
                var obj = seen[id];
                if(obj) {
                    return {
                        objectid__: id
                    }
                }
            }
            
            if(object.meta.can("prepareStorage")) {
                object.prepareStorage()
            }
            
            if(seen) {
                seen[object.identity()] = true
            }
            
            var o  = {
                classname__:   this.packedClassName(object),
                classmodule__: this.packedModuleName(object),
                objectid__:    object.identity()
            };
            
            var attrs      = object.meta.getAttributes();
            
            Joose.O.eachSafe(attrs, function packAttr (attr, name) {
                if(attr.isPersistent()) {
                    o[name]   = object[name];
                }
            })
  
            return o
        },
        
        unpack: function (classObject, data) {
            var meta      = classObject.meta
            var me        = meta.instantiate();
            var seenClass = false;
            Joose.O.eachSafe(data, function unpack (value,name) {
                if(name == "classname__") {
                    var className = value;
                    var module    = data.classmodule__
                    if(module) {
                        className = "" + module + "." + value
                    }
                    if(className != me.meta.className()) {
                        throw new Error("Storage data is of wrong type "+className+". I am "+me.meta.className()+".")
                    }
                    seenClass = true
                    return
                }
                if(name == "classmodule__") {
                    return
                }
                me[name] = value
            })
            if(!seenClass) {
                throw new Error("Serialized data needs to include a __CLASS__ attribute.: "+data)
            }
            
            if(me.meta.can("finishUnpack")) {
                me.finishUnpack()
            }
            
            return me
        },
        
        packedClassName: function (object) {
            var name   = object.meta.className();
            var parts  = name.split(".");
            return parts.pop()
        },
        
        packedModuleName: function (object) {
            var name   = object.meta.className();
            var parts  = name.split(".");
            parts.pop();
            return parts.join(".");
        }
    }
    
})

Joose.Storage.storageEngine            = Joose.Storage.Engine
Joose.Storage.jsonpickle.storageEngine = Joose.Storage.Engine.jsonpickle

})(JooseClass, JooseRole);

// ##########################
// File: Joose/Storage/Unpacker.js
// ##########################
(function (Class) {

Class("Joose.Storage.Unpacker", {
    classMethods: {
        unpack: function (data) {
            var name = data.__CLASS__;
            if(!name) {
                throw("Serialized data needs to include a __CLASS__ attribute.")
            }
            var jsName = this.packedClassNameToJSClassName(name)
            
            var co  = this.meta.classNameToClassObject(jsName);
            
            var obj = co.unpack(data);
            
            var id;
            if(Joose.Storage.CACHE && (id = data.__ID__)) {
                Joose.Storage.CACHE[id] = obj
            }
            
            return obj
        },
        
        // Format My::Class::Name-0.01 We ignore the version
        packedClassNameToJSClassName: function (packed) { 
            var parts  = packed.split("-");
            parts      = parts[0].split("::");
            return parts.join(".");
        },
        
        jsonParseFilter: function (key, value) {
            if(value != null && typeof value == "object") {
                if(value.__CLASS__) {
                    return Joose.Storage.Unpacker.unpack(value)
                }
                if(value.__ID__) {
                    return Joose.Storage.CACHE[value.__ID__]
                }
            }
            return value
        },
        
        patchJSON: function () {
            var orig = JSON.parse;
            var storageFilter = this.jsonParseFilter
            JSON.parse = function (s, filter) {
                Joose.Storage.CACHE = {}
                return orig(s, function JooseJSONParseFilter (key, value) {
                    var val = value;
                    if(filter) {
                        val = filter(key, value)
                    }
                    return storageFilter(key,val)
                })
            }
            
            var stringify = JSON.stringify;
            JSON.stringify = function () {
                Joose.Storage.TEMP_SEEN = {}
                return stringify.apply(JSON, arguments)
            }
        }
    }
})



Class("Joose.Storage.Unpacker.jsonpickle", {
    isa: Joose.Storage.Unpacker,
    classMethods: {
        unpack: function (data) {
            var name = data.classname__;
            if(!name) {
                throw("Serialized data needs to include a classname__ attribute.")
            }
            var jsName = this.packedClassNameToJSClassName(name, data.classmodule__)
            
            var co  = this.meta.classNameToClassObject(jsName);
            
            var obj = co.unpack(data);
            
            var id;
            if(Joose.Storage.CACHE && (id = data.objectid__)) {
                Joose.Storage.CACHE[id] = obj
            }
            
            return obj
        },
        
        // Format My::Class::Name-0.01 We ignore the version
        packedClassNameToJSClassName: function (className, moduleName) { 
            var name = "";
            if(moduleName) {
                name += moduleName + "."
            }
            name += className;
            return name
        },
        
        jsonParseFilter: function (key, value) {
            if(value != null && typeof value == "object") {
                if(value.classname__) {
                    return Joose.Storage.Unpacker.jsonpickle.unpack(value)
                }
                if(value.objectid__) {
                    return Joose.Storage.CACHE[value.objectid__]
                }
            }
            return value
        }
    }
})

})(JooseClass);

// ##########################
// File: Joose/Decorator.js
// ##########################
(function (Class) {
    
Class("Joose.Decorator", {
    meta: Joose.Role,
    methods: {
        decorate: function (classObject, attributeName, optionalDelegatorFuncMaker) {
            var me = this;
            var methods = classObject.meta.getInstanceMethods();
            Joose.A.each(methods, function (m) {
                var name    = m.getName();
                var argName = attributeName;
                // only override non existing methods
                if(!me.can(name)) {
                    
                    var func = function () {
                        var d = this[argName];
                        return d[name].apply(d, arguments)
                    }
                    
                    if(optionalDelegatorFuncMaker) {
                        func = optionalDelegatorFuncMaker(name)
                    }
                    
                    me.addMethod(name, func);
                }
            })
        }
    }
})

Joose.Decorator.meta.apply(Joose.Class)

})(JooseClass);

// ##########################
// File: Joose/Module.js
// ##########################

/*
Module("my.namespace", function () {
    Class("Test", {
        
    })
})
*/
(function (Class) {

Class("Joose.Module", {
    has: {
        _name: {
            is: "rw"
        },
        _elements: {
            is: "rw"
        },
        _container: {
            is: "rw"
        }
    },
    classMethods: {
        setup: function (name, functionThatCreatesClassesAndRoles) {
            var me      = this;
            var parts   = name.split(".");
            var object  = joose.top;
            var soFar   = []
            var module;
            for(var i = 0; i < parts.length; i++) {
                var part = parts[i];
                if(part == "meta") {
                    throw "Module names may not include a part called 'meta'."
                }
                var cur = object[part];
                soFar.push(part)
                var name = soFar.join(".")
                if(typeof cur == "undefined") {
                    object[part]      = {};
                    module            = new Joose.Module(name)
                    module.setContainer(object[part])
                    object[part].meta = module
                    Joose.Module._allModules.push(object[part])
                    
                } else {
                    module = cur.meta;
                    if(!(module && module.meta && (module.meta.isa(Joose.Module)))) {
                        throw "Trying to setup module "+name+" failed. There is already something else: "+module
                    }
                }
                object = object[part]
            }
            var before = joose.currentModule
            joose.currentModule = module
            if(functionThatCreatesClassesAndRoles) {
                functionThatCreatesClassesAndRoles(object);
            }
            joose.currentModule = before;
            return object
        },
        
        getAllModules: function () {
            return this._allModules
        }
    },
    methods: {
        alias: function (destination) {
            var me = this;
            
            if(arguments.length == 0) {
                return this
            }

            Joose.A.each(this.getElements(), function (thing) {
                var global        = me.globalName(thing.meta.className());
                
                if(destination[global] === thing) { // already there
                    return
                }
                if(typeof destination[global] != "undefined") {
                    throw "There is already something else in the spot "+global
                }
                
                destination[global] = thing;
            })
        },
        
        globalName: function (name) {
            var moduleName = this.getName();
            if(name.indexOf(moduleName) != 0) {
                throw "All things inside me should have a name that starts with "+moduleName+". Name is "+name
            }
            var rest = name.substr(moduleName.length + 1); // + 1 to remove the trailing dot
            if(rest.indexOf(".") != -1) {
                throw "The things inside me should have no more dots in there name. Name is "+rest
            }
            return rest
        },
        
        removeGlobalSymbols: function () {
            Joose.A.each(this.getElements(), function (thing) {
                var global = this.globalName(thing.getName());
                delete joose.top[global]
            })
        },
        
        initialize: function (name) {
            this.setElements([])
            this.setName(name);
        },
        
        isEmpty: function () {
            return this.getElements().length == 0
        },
        
        addElement: function (ele) {
            if(!(ele || ele.meta)) {
                throw "You may only add things that are Joose objects"
            }
            this._elements.push(ele)
        },
        
        getNames: function () {
            var names = [];
            Joose.A.each(this.getElements(), function (ele) { names.push(ele.meta.getName()) });
            return names
        }
    }
})
})(JooseClass);

__global__ = {};
__global__.meta = new Joose.Module();
__global__.meta.setName("__global__");
__global__.meta.setContainer(__global__);

Joose.Module._allModules = [__global__];

JooseModule("__global__.nomodule", function () {})
__global__.nomodule.meta._elements = joose.globalObjects;

// ##########################
// File: Joose/Prototype.js
// ##########################

(function (Class) {

Class("Joose.Prototype", {
    isa: Joose.Class,
    override: {
        initializer: function () {
            var init = this.SUPER()
            return function () {
                init.apply(this, arguments)
                var meta = this.meta;
                this.meta = new Joose.PrototypeLazyMetaObjectProxy();
                this.meta.metaObject = meta
                this.meta.object     = this;
            }
        }
    }
})


Class("Joose.PrototypeLazyMetaObjectProxy", {
    has: {
        metaObject: {
            is: "rw",
            isa: Joose.Class,
            handles: "*",
            handleWith: function (name) {
                return function () { 
                    // when we are called, turn the objects meta object into the original, detach yourself
                    // and call the original methods
                    var o = this.object;
                    o.meta = this.metaObject;
                    o.detach() 
                    o.meta[name].apply(o.meta, arguments)
                }
            }
        },
        object: {
            is: "rw"
        }
    }
})

Joose.bootstrap3()

})(JooseClass);

// ##########################
// File: Joose/TypeConstraint.js
// ##########################
(function (Class) {

Class("Joose.TypeConstraint", {
    has: {
        _constraints: {
            is: "ro",
            init: function () { return [] }
        },
        _coercions: {
            is: "ro",
            init: function () { return [] }
        },
        _messages: {
            is: "ro",
            init: function () { return [] }
        },
        _callback: {
            is: "ro",
            init: function() {
                return function (msg) {
                    throw new ReferenceError(msg);
                };
            }
        },
        _name: {
            is: "ro"
        },
        _uses: {
            is: "ro"
        },
        props: {
            is: "rw"
        }
    },
    
    classMethods: {
    	// name is name of type
    	// props may include: uses (Supertype), where (func) and coerce
        newFromTypeBuilder: function (name, props) {
            var t = new Joose.TypeConstraint({ name: name });
            if ( props.uses 
                 && typeof props.uses.meta != 'undefined'
                 && props.uses.meta.isa(Joose.TypeConstraint) ) {
                 t._uses = props.uses;
            }

            if(props.where) {
                t.addConstraint(props.where, props.message)
            }

            t.setProps(props)
            
            // coerce needs props from (Type) and via (func that takes current value as para and returns coerced value)
            if(props.coerce) {
                for(var i = 0; i < props.coerce.length; i++) {
                    var coercionProps = props.coerce[i];
                    t.addCoercion(new Joose.TypeCoercion({
                        from: coercionProps.from,
                        via:  coercionProps.via
                    }))
                }
            }
            
            return t
        }
    },
    
    methods: {
        
        stringify: function () {
            return this._name
        },
        
        makeSubType: function (name) {
            var t = new Joose.TypeConstraint({ name: name })
            Joose.A.each(this._constraints, function (con) {
                t.addConstraint(con)
            })
            return t
        },
        
        addCoercion: function (coercion) {
            this._coercions.push(coercion);
        },
        
        addConstraint: function (func, message) {
            this._constraints.push(func);
            this._messages.push(message)
        },
        
        getConstraintList: function () {
            var cons = this._constraints;
            if ( this._uses ) {
                var parentcons = this._uses.getConstraintList();
                return parentcons.concat(cons);
            }
            return cons;
        },
        
        getMessageList: function () {
            var msg = this._messages;
            if ( this._uses ) {
                var parentmsg = this._uses.getMessageList();
                return parentmsg.concat(msg);
            }
            return msg;
        },

        validateBool: function (value) {
            var i = this._validate(value);
            if(i == -1) {
                return true
            }
            return false
        },
        
        validate: function (value) {
            var i = this._validate(value);
            if(i == -1) {
                return true
            }
            var messages = this.getMessageList();
            var message = messages[i] 
                ? messages[i].call(this,value)
                : "The passed value ["+value+"] is not a "+this;
            this._callback(message);
        },
        
        _validate: function (value) {
            var con = this.getConstraintList();
            var i, len;
            for(i = 0, len = con.length; i < len; i++) {
                var func = con[i];
                var result = false;
                if(func instanceof RegExp) {
                    result = func.test(value)
                } else {
                    result = func.call(this, value)
                }
                
                if(!result) {
                    return i
                    
                }
            }
            return -1
        },

        coerce: function (value) {
            if(this.validateBool(value)) {
                return value
            }
            //alert("in constraints coerce call: "+value);
            var coercions = this._coercions;
            for(var i = 0, len = coercions.length; i < len; i++) {
                var coercion = coercions[i];
                var result   = coercion.coerce(value);
                if(result !== null) {
                    return result
                }
            }
            return null
        }
    }
});

})(JooseClass);

// ##########################
// File: Joose/TypeCoercion.js
// ##########################
(function (Class, Type) {

//TODO this is a hack to fix the conflict between 
//type constraints and isa object constraints. It 
//probably needs  more elegant solution.
Type('CoercionFrom', {
    where: function(o) {
        if ( o.meta && o.meta.isa(Joose.TypeConstraint) ) {
            return true;
        }
        return false;
    }
});

Class("Joose.TypeCoercion", {
    has: {
        _from: {
            isa: TYPE.CoercionFrom,
            is:  "rw"
        },
        _via: {
            is: "rw"
        }
    },
    
    methods: {
        coerce: function (value) {
            if(this._from.validateBool(value)) {
                return this._via(value)
            }
            return null
        }
    }
})

})(JooseClass, JooseType);

// ##########################
// File: Joose/Types.js
// ##########################
(function (Type) {
	Type('Any', {
	    // Returns true for any type
	    where: function(o) {
			return true
	    }
	});


	Type('Null', {
	    uses: TYPE.Any,
	    where: function(o) {
	        if (o === null) {
	            return true;
	        }
	        return false;
	    }
	});
	
	Type('NotNull', {
	    uses: TYPE.Any,
	    where: function(o) {
	        if (o === null) {
	            return false;
	        }
	        return true;
	    }
	});

	Type('Enum', {
	    uses: TYPE.NotNull,
	    message: function(v) {
	        return "The passed value ["+v+"] is not "+
	               (this.getProps().strictMatch?"*strictly* ":"")+
	               "one of ["+this.getProps().values.join(",")+"]";
	    },
	    where: function (v) {
	        var self = this;
	        if ( !self.getProps() || self.getProps().values === undefined || !(self.getProps().values instanceof Array)) {
	            throw "Enum Type needs Array of values in 'values' property of Type declaration"
	        }
	        var eq = function(vv) {
	            if (self.getProps().strictMatch === true) return (vv === v);
	            return (vv == v);
	        }
	        if ( Joose.A.grep(self.getProps().values, eq).length != 0 ) {
	            return true;
	        }
	        return false;
	    }
	});

	Type('Obj', {
	    uses: TYPE.NotNull,
	    where: function (o) {
	        if ( o instanceof Object ) {
	            return true;
	        }
	        return false;
	    }
	});

	Type('Str', {
	    uses: TYPE.NotNull,
	    where: function(S) {
	        if ( typeof S == 'string' || S instanceof String ) {
	            return true;
	        }
	        return false
	    },
	    coerce: [{
	        from: TYPE.Any,
	        via:  function (value) {
	            if(value == null) {
	                return ""
	            } else {
	                return "" + value
	            }
	        }
	    }]
	});

	Type('Num', {
	    uses: TYPE.NotNull,
	    where: function(N) {
	        if ( typeof N == 'number' || N instanceof Number ) {
	            return true;
	        }
	        return false
	    },
	    coerce: [{
	        from: TYPE.Str,
	        via:  function (value) {
	            if(value == null || value == "") return undefined;
	            // TODO parse for valid format
	            return parseFloat(value)
	        }
	    }]
	});

	Type('Bool', {
	    uses: TYPE.NotNull,
	    where: function(B) {
	        if (B === true || B === false) {
	            return true;
	        }
	        return false;
	    },
	    coerce: [{
	        from: TYPE.Any,
	        via:  function (value) {
	            if(value == null || value === "") return undefined;
	            if(value == 1 || value == "1" || value == "true") {
	                return true
	            }
	            if(value == 0 || value == "0" || value == "false" ) {
	                return false
	            }
	            return null
	        }
	    }]
	});

	Type('Int', {
	    uses: TYPE.Num,
	    where: function(n) {
	        var sn = String(n);
	        if ( sn.match(/^\d*\.\d$/) ) {
	            return false;
	        }
	        return true;
	    },
	    coerce: [{
	        from: TYPE.Str,
	        via:  function (value) {
	            if(value == null || value == "") return undefined;
	            if(value.match(/^-{0,1}\d+$/)) {
	                return parseInt(value)
	            }
	            return
	        }
	    }]
	});

	//TODO(jwall): Float is starting to look superfluous Floats are a superset of Int
	//and javascript has no good way to differentiate between Num and Float
	//It's only benefit is semantic sugar. TYPE.Float = TYPE.Num?
	Type('Float', {
	    uses: TYPE.Num,
	    where: function(n) {
	        return true
	    }
	});

	Type('Func', {
	    uses: TYPE.Obj,
	    where: function (f) {
	        if ( typeof f == 'function' ) {
	            return true;
	        }
	        return false;
	    }
	});

	Type('Array', {
	    uses: TYPE.Obj,
	    where: function (A) {
	        if ( A instanceof Array ) {
	            return true;
	        }
	        return false;
	    }
	});

	Type('Date', {
	    uses: TYPE.Obj,
	    where: function (D) {
	        if ( D instanceof Date ) {
	            return true;
	        }
	        return false;
	    },
	    coerce: [{
	        from: TYPE.Str,
	        via:  function (value) {
	            var match;
	            if(value == undefined || value == "") {
	                return undefined;
	            } else if(match = value.match(/\s*(\d+)-(\d+)-(\d+)/)) {
	                return new Date(match[1], match[2]-1, [match[3]])
	            }
	            return null
	        }
	    }]
	});

	Type('Joose', {
	    uses: TYPE.Obj,
	    where: function (o) {
	        //TODO not sure if this is correct yet.
	        if ( o.meta && o.meta.meta.isa(Joose.Class) ) {
	            return true;
	        }
	        return false;
	    }
	});	
})(JooseType);

;
// ##########################
// File: /js/Addressable/Cookie.js
// ##########################
Module("Addressable", function () {
    Class("Cookie", {
        
        methods: {
        
            initialize: function () {
                this.doc = document;
            },

            /*
             * Retrieve a cookie called $name
             */
            // Extremely ugly code that seems to work follows. a more robust replacement is more that welcome
            get: function (name) {
                       
                var dc   = this.doc.cookie;
        
        
                var prefix = name + "=";
                var begin  = dc.indexOf("; " + prefix);
                if (begin == -1) {
                        begin = dc.indexOf(prefix);
                        if (begin != 0) return ""; // Wenn der Name (Prefix) ohne vorgestelltes ; nicht am Zeilenanfang steht, dann ist er Teil eines anderen Cookies und somit nicht was wir suchen.
                } else {
                        begin += 2 // Plus 2 damit der Index nicht mehr auf dem ; steht
                }
                var end = this.doc.cookie.indexOf(";", begin);
                if (end == -1) { // Wenn kein ; vorhanden ist, dann handelt es sich um den letzten Wert im Cookie-String. Somit ist das Ende des Cookie-Strings auch gleich das ende des gesuchten Wertes.
                        end = dc.length;
                }
                var value = unescape(dc.substring(begin + prefix.length, end)); // Der Wert des gesuchten Cooki wird als Teilstring aus dem gesamten Cookie-Strings extrahiert.
        
                if(value == ";") { // bug with IE
                        return ""
                }
        
                return value;
            },
               
            /*
             * Set a cookie with name and value
             * expires must be a Date-Object
             */
            set: function(name, value, expires, secure) {
               
               if(value == null) {
                   value = "";
               }
        
                        var cookie = name + "=" + escape(value) +
                        ( ( expires ) ? "; expires=" + expires.toGMTString() : "" ) +
                        //((path) ? "; path=" + path : "") +
                        "; path=/" +
                        ((secure) ? "; secure" : "");
        
                this.doc.cookie = cookie;
            }
        }
    })

})
;
// ##########################
// File: /js/Addressable/Constants.js
// ##########################
Module("Addressable", function (m) {
    Class("Constants", {
        classMethods: {
            appHost: function () {
                return this.isLocal() ? "self:8084" : "universal-comet.appspot.com"
            },
            
            insideGearsWorker: function () {
                return Addressable.GEARS ? true : false // global set in gearsWorkers.js
            },
            
            gearsWorkerFile: function () {
                return this.isLocal() ? "/gears/gears-client-server.js" : "/gears/gears-client-server-mini.js"
            },
            
            activeChannelExpirationSeconds: function () {
                return 5
            },
            
            cometRequestInterval: function () {
                return 2000
            },
            
            isLocal: function () {
                return window.__LOCAL__ == true
            }
        }
    })
})
;
// ##########################
// File: /js/Addressable/Connection.js
// ##########################
Module("Addressable", function () {
    Role("Connection", {
        requires: ["get"]
    })
})
;
// ##########################
// File: /js/Addressable/CometClient.js
// ##########################
Module("Addressable", function() {
    
    Class("CometClient", {
        
        has: {
            url: {
                is: "rw",
                required: true
            },
            callback: {
                is: "rw",
                required: true
            },
            
            server: {
                is: "rw",
                required: true
            },
            
            doDisconnect: {
                is: "rw",
                init: false
            },
            
            logger: {
                is: "rw",
                required: true
            },
            
            connection: {
                isa: Addressable.Connection,
                is: "rw",
                required: true
            },
            
            requestCounter: {
                init: 0
            },
            
            useGears: {
                
            }
        },
        
        methods: {
            
            disconnect: function () {
                this.setDoDisconnect(true)
            },
        
            listen: function () {
                var self    = this;
                var handleResponse = function (text) {
                    self.handleResponse(text);
                    if(!self.doDisconnect) {
                        self.getTimer().setTimeout(function () {
                            self.listen();
                        }, Addressable.Constants.cometRequestInterval())
                    }
                }
                
                this.connection.get(this.getUrl(), this.getServer().getListenParas(), handleResponse, function (err) {
                    self.logger.log(err)
                })
            },
            
            handleResponse: function () {
                try {
                    this.getCallback().apply(this, arguments)
                } catch(e) {
                    this.logger.log("Error: "+e)
                }
            },
            
            getTimer: function () {
                return this.getServer().getTimer()
            }
        }

    })
})
;
// ##########################
// File: /js/Addressable/XDomainRequest.js
// ##########################
Module("Addressable", function () {
    
    var connection;
    
    Class("XDomainRequest", {
        classMethods: {
            getConnection: function () {
        
                if(connection) {
                    return connection
                }
        
                if(Addressable.Constants.insideGearsWorker()) {
                    connection = new Addressable.GearsRequest();
                } else {
                    connection = new Addressable.ScriptRequest();
                }
                return connection
            }
        }
    })
})
;
// ##########################
// File: /js/Addressable/Server.js
// ##########################
Module("Addressable", function () {
    Class("Server", {
        
        has: {
            implementation: {
                is: "rw"
            },
            
            channel: {
                is: "rw"
            },
            
            useGears: {
                is: "rw",
                init: true
            },
            
            onmessage: {
                is: "rw"
            }
        },
        
        after: {
            initialize: function () {
                this.setImplementation( this._serverFactory() )
            }
        },
        
        methods: {
            connect: function (onConnect) {
                this.implementation.connect(onConnect)
            },
            
            _serverFactory: function () {
                if(this.clientCanGears()) {
                    return new Addressable.GearsServerStub({ facade: this });
                } else {
                    return new Addressable.SimpleServer({ facade: this });
                }
            },
            
            clientCanGears: function () {
                if(this.useGears) {
                    JooseGearsInitializeGears()
                    return window.google && google.gears
                }
                return false
            },
            
            subscribe: function (scope, onSuccess) {
                
                this.implementation.subscribe(scope, onSuccess)
            },
            
            // posts to a subscription/scope
            post: function (scope, message, onSuccess) {
                this.implementation.post(scope, message, onSuccess)
            },
        }
        
    })
})
;
// ##########################
// File: /js/Addressable/SimpleServer.js
// ##########################
Module("Addressable", function () {
    
    var ID_COOKIE       = "AddressableID";
    var URL_COOKIE      = "AddressableURL";
    var CHANNEL_COOKIE  = "AddressableChannel";
    
    var ACTIVITY_COOKIE = "AddressableActive";
    
    var REQUEST_COUNT   = 0;
    
    Type("AddressableChannel", {
        uses: TYPE.Str,
        where: function (str) {
            if(str.match(/^\[a-z0-9]+$/)) {
                return true
            } else {
                return false
            }
        }
    })
    
    Class("SimpleServer", {
        has: {
            cometClient: {
                is: "rw"
            },
            
            id: {
                is: "rw"
            },
            
            url: {
                is: "rw"
            },
            
            referrer: {
                is: "rw",
                init: function () { return location.href }
            },
            
            cookie: {
                init: function () { return new Addressable.Cookie() }
            },
            
            // channels differentiate between different windows
            // If there is anything in window.name we use that, otherwise we set window.name to make the channel name persistent per session
            channel: {
                isa: TYPE.AddressableChannel,
                is: "rw",
                init: function () { 
                    if(window.name) {
                        return window.name
                    } else {
                        window.name = "ch"+Math.floor(Math.random() * 1000);
                        return window.name
                    }
                } // Taking chances
            },
            
            // the Addressable.Server object
            facade: {
                is: "rw"
            }
        },
        
        after: {
            initialize: function () {
                var cookie = this.getCookies();
                if(!this.id) {
                    this.id = cookie.id
                }
                if(!this.url) {
                    this.url = cookie.url
                }
            }
        },
        
        methods: {
            
            getCookies: function () {
    
                return {
                    id: this.cookie.get(ID_COOKIE),
                    url: this.cookie.get(URL_COOKIE)
                }
            },
            
            clearUrl: function (url) { // remove channel from saved url
                url = url.replace(/-[a-z0-9]+$/, "")
                return url
            },
            
            setCookies: function (id, url) {
                if(id && url) {
                    
                    url = this.clearUrl(url);
                    
                    this.cookie.set(ID_COOKIE, id)
                    this.cookie.set(URL_COOKIE, url)
                }
            },
            
            getListenIds: function () { // Be default only one id
                return this.getId()
            },
            
            getListenParas: function () {
                return {
                    ids:      this.getListenIds(),
                    referrer: this.getReferrer(),
                    count:    REQUEST_COUNT++
                }
            },
            
            handleConnect: function (callback, id, url) {
                var self = this;
                self.setId(id)
                
                var channel = self.getChannel();
                if(channel) {
                    self.log("URL "+url)
                    url  = this.clearUrl(url) // remove channel from saved url
                    url += "-"+channel
                }
                
                self.setUrl(url);
                callback.call(self, id, url);
                
                var interval = self.getTimer().setInterval(function () {
                    if(self.passiveMode()) {
                        self.pollDataStore()
                    } else {
                        self.getTimer().clearInterval(interval)
                        self.log("Start listening")
                        self.getCometClient().listen();
                    }
                }, 500)
            },
            
            connect: function (callback) {
                var self       = this;
                var connection = Addressable.XDomainRequest.getConnection();
            
                var cometClient = new Addressable.CometClient({
                    connection: connection,
                    server:     self,
                    callback:   self.requestHandler(),
                    logger:     self,
                    url:        self.listenUrl(),
                    useGears:   self.useGears()
                })
                self.setCometClient(cometClient)
               
                if(this.id && this.url) {
                    self.handleConnect(callback, this.id, this.url)
                    self.log("Saved connection "+this.url + "id: "+this.id)
                    return
                }
                
                var paras = { 
                    time: new Date().getTime()
                }
                if(Addressable.Constants.isLocal()) {
                    paras.__test__ = 1;
                }
                connection.get(this.connectUrl(), paras, function (data) {
                    self.log("Connection successful "+data.url + "id: "+data.id)
                    self.handleConnect(callback, data.id, data.url)
                    self.setCookies(data.id, data.url)
                })
            },
            
            useGears: function () {
                return false
            },
            
            sendToOtherChannel: function (request) {
                var name = CHANNEL_COOKIE+"-"+request.id+"-"+request.channel;
                this.log("Send to "+name)
                this.cookie.set(name, JSON.stringify(request))
            },
            
            pollDataStore: function () {
                var name = CHANNEL_COOKIE+"-"+this.id+"-"+this.getChannel();
                var value = this.cookie.get(name);
                if(value) {
                    this.log("Got value from data store")
                    this.cookie.set(name,"");
                    var request = JSON.parse(value);
                    this.processRequest(request, request.id)
                }
            },
            
            passiveMode: function () {
                var val = this.cookie.get(ACTIVITY_COOKIE)
                var now = new Date().getTime()
                //this.log("Las activity "+val)
                if(val && now - parseInt(val,10) < Addressable.Constants.activeChannelExpirationSeconds() * 1000) {
                    //this.log("passive")
                    return true
                }
                this.log("active")
                return false
            },
            
            signalActivity: function () {
                var now    = new Date().getTime()
                //this.log("Signal activity")
                this.cookie.set(ACTIVITY_COOKIE, now)
            },
            
            processRequest: function (request, id) {
                var self      = this;
                var myChannel = self.getChannel();
                request.id    = id;
                var channel   = request.channel;
                if(channel   != myChannel || id != this.id) {
                    self.sendToOtherChannel(request)
                    return // continue
                }
                var message   = request.message;
                
                self.handleMessage(request)
            },
            
            handleMessage: function (request) {
                if(this.facade.onmessage) {
                    this.facade.onmessage.call(request, request.message)
                } else {
                    this.postMessage(request.message)
                }
            },
            
            postMessage: function (message) {
                if(window.postMessage) {
                    var event = document.createEvent("MessageEvent");
                    event.initMessageEvent("message", false, false, message, "client-server.appspot.com", location.href, window);
                    window.dispatchEvent(event)
                }
            },
            
            requestHandler: function () {
                var self = this;
                
                return function requestCallback (data) {
                    self.signalActivity();
                    Joose.O.each(data, function (requests, id) {
                        Joose.A.each(requests, function (request) {
                            self.processRequest(request, id)
                        })
                    })
                }
            },
            
            // subscribe to a scope
            subscribe: function (scope, onSuccess) {
                
                var id  = encodeURIComponent(this.getId()+"-"+this.getChannel());
                scope   = encodeURIComponent(scope);
                
                var url = "https://"+Addressable.Constants.appHost()+"/subscribe/"+id+"/"+scope
                
                Addressable.XDomainRequest.getConnection().get(url, null, onSuccess)
            },
            
            // posts to a subscription/scope
            post: function (scope, message, onSuccess) {
                scope   = encodeURIComponent(scope);
                
                var url = "https://"+Addressable.Constants.appHost()+"/post/"+scope
                
                Addressable.XDomainRequest.getConnection().get(url, { message: message }, onSuccess)
            },
            
            connectUrl: function () {
                return "https://"+Addressable.Constants.appHost()+"/connect"
            },
            
            listenUrl: function () {
                return "https://"+Addressable.Constants.appHost()+"/listen"
            },
            
            log: function (msg) {
                if(window.console)
                    console.log(this.meta.className() + ": "+ msg)
            },
            
            getTimer: function () {
                return window
            }
        }
    })
})
;
// ##########################
// File: /js/Addressable/GearsServerStub.js
// ##########################
Module("Addressable", function () {
    
    // Starts 
    
    Class("GearsServerStub", {
        isa: Addressable.SimpleServer,
        
        has: {
            wp:       {},
            workerId: {}
        },
        
        override: {
            connect: function (onConnect) {
                try {
                    this._connect(onConnect)
                } catch(e) {
                    this.SUPER(onConnect); // try without gears
                }
            }
        },
        
        methods: {
            _connect: function (onConnect) {
                var self = this;
                var wp   = google.gears.factory.create('beta.workerpool');
                this.wp  = wp;
                
                var cookie = this.getCookies()
            
                this.workerId = wp.createWorkerFromUrl("https://"+Addressable.Constants.appHost()+"/gears/gears-client-server.js");
                self.log("Starting worker")
                wp.sendMessage({ 
                    event: "connect",
                    data: {
                        id:  cookie.id || "",
                        url: cookie.url || "",
                        referrer: location.href,
                        channel:  self.channel,
                        isLocal:  Addressable.Constants.isLocal()
                    }
                }, this.workerId)
                
                var requestHandler = self.requestHandler();
                
                wp.onmessage = function(a, b, message) {
                    var body = message.body;
                    
                    if(body.event == "connect") {
                        self.log("received connect event "+body.data.url)
                        if(onConnect) {
                            onConnect(body.data.id, body.data.url)    
                        }
                        self.setCookies(body.data.id, body.data.url)
                    }
                    else
                    if(body.event == "request") {
                        self.log("received request event "+body.data.message)
                        self.handleMessage(body.data)
                    }
                    else
                    if(body.event == "log") {
                        self.log(body.msg)
                    } else {
                        self.log("received unknown event "+body.event)
                    }
                }
            }
        }
        
    })
})
;
// ##########################
// File: /js/Addressable/ScriptRequest.js
// ##########################
Module("Addressable", function () {
    
    var counter = 0;
    var timeout;
    
    Class("ScriptRequest", {
        does: Addressable.Connection,
        
        methods: {
            get: function (url, data, callback) {
                var self = this;
                data = data || {};
                data.__NO_CACHE__      = Math.random();
                data.__REQUEST__ID__   = counter++;
                data.__STRATEGY__      = "script"
                
                var dataString = ""
                if (data) {
                    for ( var i in data) {
                        dataString += encodeURIComponent(i) + "="
                                + encodeURIComponent(data[i]) + "&"
                    }
                }
                if (data) {
                    url += "?" + dataString
                }
            
                var script = document.createElement("script");
                script.src = url
                
                var target = document.getElementsByTagName("body")[0]
                if(target == null) {
                    target = document.getElementsByTagName("head")[0]
                }

                target.appendChild(script);
                
                this.meta.c.Requests[data.__REQUEST__ID__] = {
                    target:   target,
                    tag:      script,
                    callback: function () {
                        this.target.removeChild(this.tag)
                        delete self.meta.c.Requests[data.__REQUEST__ID__] 
                        if(typeof callback == "function") {
                            callback.apply(window, arguments)
                        } 
                    }
                }
            }
        }
    })
    
    window.Addressable.ScriptRequest.Requests = {};
})
})()
