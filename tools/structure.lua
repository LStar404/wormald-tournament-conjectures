local environments = {
  definition = "definition", theorem = "theorem", lemma = "lemma",
  corollary = "corollary", external = "externaltheorem",
  example = "example", notation = "notationblock", proof = "structuredproof"
}
local function escape_tex(s)
  return s:gsub("\\", "\\textbackslash{}")
    :gsub("([%%&#_$])", "\\%1"):gsub("{", "\\{"):gsub("}", "\\}")
end
function Div(el)
  local env = environments[el.classes[1]]
  if not env then return nil end
  local title = escape_tex(el.attributes.title or "")
  local opening
  if env == "structuredproof" or env == "notationblock" then
    opening = "\\begin{" .. env .. "}{" .. title .. "}"
  else
    opening = "\\begin{" .. env .. "}[" .. title .. "]"
  end
  if env == "structuredproof" then
    local last = el.content[#el.content]
    if last and (last.t == "Para" or last.t == "Plain") then
      local tail = last.content[#last.content]
      if not (tail and tail.t == "Math" and tail.mathtype == "DisplayMath") then
        last.content:insert(pandoc.RawInline("latex", "\\nobreak\\hfill\\ensuremath{\\square}"))
      end
    end
  end
  local result = pandoc.List({pandoc.RawBlock("latex", opening)})
  result:extend(el.content)
  result:insert(pandoc.RawBlock("latex", "\\end{" .. env .. "}"))
  return result
end
function Math(el)
  if el.mathtype == "InlineMath" and el.text:match("^r_d=\\lim") then
    el.text = el.text:gsub("/", "\\allowbreak/\\allowbreak")
  end
  return el
end
function BulletList(el)
  if #el.content <= 3 and #pandoc.utils.stringify(el) < 180 then
    return {pandoc.RawBlock("latex", "\\begin{samepage}"), el,
            pandoc.RawBlock("latex", "\\end{samepage}")}
  end
end
