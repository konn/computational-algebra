const jsdom = require('jsdom');
const {JSDOM} = jsdom;
const dom = new JSDOM(require('fs').readFileSync('/dev/stdin', 'utf8'));
document = dom.window.document;
katex = require('../katex/katex.js');
const renderMathInElement = require('../katex/contrib/auto-render.js');
renderMathInElement(document.body, {
    delimiters:
    [ {left: "\\(", right: "\\)", display: false },
      {left: "\\[", right: "\\]", display: true }
    ]
});
process.stdout.write(dom.serialize());
