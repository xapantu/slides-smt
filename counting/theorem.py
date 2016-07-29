from __future__ import print_function
import pandocfilters as pf
import sys

def eprint(*args, **kwargs):
    print(*args, file=sys.stderr, **kwargs)

def latex(s):
    return pf.RawBlock('latex', s)



def stringify_maths(x):
    """Walks the tree x and returns concatenated string content,
    leaving out all formatting.
    """
    result = []

    def go(key, val, format, meta):
        if key in ['Str', 'MetaString']:
            result.append(val)
        elif key == 'Code':
            result.append(val[1])
        elif key == 'Math':
            result.append("$" + val[1] + "$")
        elif key == 'LineBreak':
            result.append(" ")
        elif key == 'Space':
            result.append(" ")

    pf.walk(x, go, "", {})
    return ''.join(result)

def mk_columns(k, v, f, m):
    if k == "Para":
        if type(v[0]['c']) == unicode and v[0]['c'].startswith('Lemma['):
            b = []
            v[0]['c'] = v[0]['c'][len('Lemma['):]
            found = False
            c = []
            for a in v:
                if not found:
                    if type(a['c']) == unicode and a['c'].endswith("]:"):
                        a['c'] = a['c'][:-2]
                        found = True
                    else:
                        b.append(a)
                else:
                    c.append(a)
            if found:
                #c.insert(0, latex(r'\begin{lemma}'))
                #c.append(latex(r'\end{lemma}'))
                return [latex(r"\begin{lemma}[" + stringify_maths(b) + "]"), pf.Para(c), latex(r"\end{lemma}")]

if __name__ == "__main__":
    pf.toJSONFilter(mk_columns)
