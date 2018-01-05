(function e(t,n,r){function s(o,u){if(!n[o]){if(!t[o]){var a=typeof require=="function"&&require;if(!u&&a)return a(o,!0);if(i)return i(o,!0);var f=new Error("Cannot find module '"+o+"'");throw f.code="MODULE_NOT_FOUND",f}var l=n[o]={exports:{}};t[o][0].call(l.exports,function(e){var n=t[o][1][e];return s(n?n:e)},l,l.exports,e,t,n,r)}return n[o].exports}var i=typeof require=="function"&&require;for(var o=0;o<r.length;o++)s(r[o]);return s})({1:[function(require,module,exports){
"use strict";

/* global katex */

{
    var scripts = document.body.getElementsByTagName("script");
    scripts = Array.prototype.slice.call(scripts);
    scripts.forEach(function (script) {
        if (!script.type || !script.type.match(/math\/tex/i)) {
            return -1;
        }
        var display = script.type.match(/mode\s*=\s*display(;|\s|\n|$)/) != null;

        var katexElement = document.createElement(display ? "div" : "span");
        katexElement.setAttribute("class", display ? "equation" : "inline-equation");
        try {
            katex.render(script.text, katexElement, { displayMode: display });
        } catch (err) {
            //console.error(err); linter doesn't like this
            katexElement.textContent = script.text;
        }
        script.parentNode.replaceChild(katexElement, script);
    });
}

},{}]},{},[1]);
