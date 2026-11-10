-- Pandoc filter for the PDF editions (Verification.pdf, ProofByProof.pdf).
-- Inline code here is mostly Lean declaration names: long words that LaTeX cannot break,
-- so they ran past the right margin. Emit them as \texttt with a break point after
-- each '.', '_', '/' and ','.
if not FORMAT:match('latex') then return {} end

local map = {
  ['\\'] = '\\textbackslash{}', ['{'] = '\\{', ['}'] = '\\}', ['$'] = '\\$',
  ['&'] = '\\&', ['#'] = '\\#', ['%'] = '\\%', ['~'] = '\\textasciitilde{}',
  ['^'] = '\\textasciicircum{}', ['_'] = '\\_\\allowbreak{}',
  ['.'] = '.\\allowbreak{}', ['/'] = '/\\allowbreak{}', [','] = ',\\allowbreak{}',
}

function Code(el)
  local out = {}
  for ch in el.text:gmatch('[%z\1-\127\194-\244][\128-\191]*') do
    out[#out + 1] = map[ch] or ch
  end
  return pandoc.RawInline('latex', '\\texttt{' .. table.concat(out) .. '}')
end
