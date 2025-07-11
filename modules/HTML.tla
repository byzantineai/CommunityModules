Write a module that implements HTML generation utilities for creating web documents programmatically.

HTMLFill performs template substitution by replacing placeholders with values from a sequence of tuples.
HTMLDocument creates a complete HTML document with header, body, and scripts.
HTMLClass generates CSS class definitions with a list of attributes.
HTMLAttribute creates CSS attribute declarations with name-value pairs.
HTMLStyleSheet builds a complete style sheet with default styles and custom classes.
HTMLScriptFile includes external JavaScript files by reference.
HTMLScript embeds inline JavaScript code within script tags.
HTMLHeader constructs the document head with title, links, and styles.
HTMLBody wraps content in body tags.
HTMLFrame creates div containers with specified IDs.
HTMLGridContainer generates grid layout containers with custom classes.
HTMLBox creates styled div elements with borders and custom sizing.
HTMLCircle extends HTMLBox to create circular elements.
HTMLText wraps text content in span elements with IDs.
HTMLSVG embeds SVG graphics with viewBox and size specifications.
HTMLSize generates width and height style attributes.
HTMLJSLine creates LeaderLine connections between elements.
HTMLJSKeyListener implements keyboard event handling for navigation.

-------------------------------- MODULE HTML --------------------------------

LOCAL INSTANCE Sequences
LOCAL INSTANCE SequencesExt

\***** Helpers

HTMLFill(string, args) ==
    (***********************************************************************)
    (* Do the sequence of replaces in args to the string.                  *)
    (* The args is a sequence of tuples: <<substr,newsubstr>>.             *)
    (* Example:                                                            *)
    (*     HTMLFill("test %num%", << <<"%num%", "12">> >>) = "test 12"     *)
    (***********************************************************************)
    LET f(str, x) == ReplaceFirstSubSeq(x[2], x[1], str)
    IN FoldLeft(f, string, args)

LOCAL StringSeqToString(string_seq, separator) ==
    (***********************************************************************)
    (* Concatenates sequence of strings into one string.                   *)
    (* The `seperator` is put between the strings in the sequence.         *)
    (* Example:                                                            *)
    (*     StringSeqToString(<<"Test","string!">>, "-") = "Test-string!"   *)
    (***********************************************************************)
    LET f(str1,str2) == IF str1 = "" THEN str2 ELSE str1 \o separator \o str2
    IN FoldLeft(f, "", string_seq)

\***** Main Document

HTMLDocument(header, body, list_of_scripts) ==
    StringSeqToString(<<
        "<!DOCTYPE html>",
        "<html>",
        header,
        body,
        StringSeqToString(list_of_scripts,"\n"),
        "</html>"
    >>, "\n")

\***** Style Sheet

HTMLClass(classname, attribute_list) ==
    StringSeqToString(<<
        ReplaceFirstSubSeq(classname, "%classname%", "%classname% {"),
        StringSeqToString(attribute_list,"\n"),
        "}"
    >>, "\n")

HTMLAttribute(name, value) ==
    HTMLFill("%name%: %value%;", <<
        <<"%name%", name>>,
        <<"%value%", value>>
    >>)

HTMLDefaultStyle ==
    StringSeqToString(<<
        HTMLClass(".default_grid",<<
            HTMLAttribute("display", "grid")
        >>),
        HTMLClass(".default_box",<<
            HTMLAttribute("border", "1px solid black")
        >>),
        HTMLClass(".default_circle",<<
            HTMLAttribute("border-radius", "50%")
        >>)
    >>, "\n")

HTMLStyleSheet(class_list) ==
    StringSeqToString(<<
        "<style type=\"text/css\">",
        HTMLDefaultStyle,
        StringSeqToString(class_list,"\n"),
        "</style>"
    >>, "\n")

\***** Script

HTMLScriptFile(name) ==
    HTMLFill("<script src=\"%name%\"></script>", << <<"%name%", name>>>> )

HTMLScript(children) ==
    StringSeqToString(<<
        "<script>",
        StringSeqToString(children, "\n"),
        "</script>"
    >>, "\n")

\***** Header

HTMLLink(name, type) ==
    HTMLFill("<link href=\"%name%\" rel=\"%type%\"/>",
        << <<"%name%", name>>, <<"%type%", type>> >> )

HTMLHeader(title, list_of_links, class_list) ==
    StringSeqToString(<<
        "<head>",
        "<meta charset=\"UTF-8\">",
        ReplaceFirstSubSeq(title, "%title%", "<title>%title%</title>"),
        StringSeqToString(list_of_links,"\n"),
        HTMLStyleSheet(class_list),
        "</head>"
    >>, "\n")

\***** Body

HTMLBody(body) ==
    StringSeqToString(<<
        "<body>",
        body,
        "</body>"
    >>, "\n")

HTMLFrame(id, children) ==
    StringSeqToString(<<
        ReplaceFirstSubSeq(id, "%id%", "<div id=\"%id%\">"),
        StringSeqToString(children, "\n"),
        "</div>"
    >>, "\n")

HTMLGridContainer(id, class_list, children) ==
    StringSeqToString(<<
        HTMLFill("<div id=\"%id%\" class=\"default_grid %class_list%\">",<<
            <<"%id%", id>>,
            <<"%class_list%", StringSeqToString(class_list, " ")>>
        >>),
        StringSeqToString(children, "\n"),
        "</div>"
    >>, "\n")

HTMLBox(id, class_list, size, children) ==
    StringSeqToString(<<
        HTMLFill("<div id=\"%id%\" class=\"default_box %class_list%\" style=\"%size%\">",<<
            <<"%id%", id>>,
            <<"%class_list%", StringSeqToString(class_list, " ")>>,
            <<"%size%", size>>
        >>),
        StringSeqToString(children, "\n"),
        "</div>"
    >>, "\n")

HTMLCircle(id, class_list, size, children)  ==
    HTMLBox(id, <<"default_circle">> \o class_list, size, children)

HTMLText(id, text) ==
    StringSeqToString(<<
        ReplaceFirstSubSeq(id, "%id%", "<span id=\"%id%\">"),
        text,
        "</span>"
    >>, "\n")

HTMLSVG(id, viewBox, size, svgString) ==
    StringSeqToString(<<
        HTMLFill("<svg id=\"%id%\" viewBox=\"%viewBox%\" style=\"%size%\">",<<
            <<"%id%", id>>,
            <<"%viewBox%", viewBox>>,
            <<"%size%", size>>
        >>),
        svgString,
        "</svg>"
    >>, "\n")

\***** Pre built

HTMLSize(width, height) ==
    StringSeqToString(<<
        HTMLAttribute("width", width),
        HTMLAttribute("height", height)
    >>, " ")

HTMLNewLine ==
    "<br>"

HTMLFlexCenterAttributes ==
    StringSeqToString(<<
        HTMLAttribute("display", "flex"),
        HTMLAttribute("align-items", "center"),
        HTMLAttribute("justify-content", "center")
    >>,"\n")

HTMLJSLineElems(fromID, destID) ==
    HTMLFill("document.getElementById(\"%id1%\"), document.getElementById(\"%id2%\")",
        << <<"%id1%", fromID>>, <<"%id2%", destID>> >> )

HTMLJSLine(fromID, destID, color, size) ==
    HTMLFill("new LeaderLine(%elems%, {color: '%color%', size: %size%})",
    << <<"%elems%", HTMLJSLineElems(fromID, destID)>>,
       <<"%color%", color>>, <<"%size%", size>> >> )

HTMLJSLineDash(fromID, destID, color, size) ==
    HTMLFill("new LeaderLine(%elems%,  {color: '%color%', size: %size%, dash: true})",
    << <<"%elems%", HTMLJSLineElems(fromID, destID)>>,
       <<"%color%", color>>, <<"%size%", size>> >> )

HTMLJSKeyListener(events) ==
    StringSeqToString(<<
        "window.onkeyup = function(event) {",
        "let key = event.key.toUpperCase();",
        StringSeqToString(events,"\n"),
        "}"
    >>, "\n")

HTMLJSNavigationKey(key, file) ==
    StringSeqToString(<<
        ReplaceFirstSubSeq(key, "%key%", "if(key == '%key%'){"),
        ReplaceFirstSubSeq(file, "%file%", "window.location.replace(\"%file%\");"),
        "}"
    >>,"\n")
=============================================================================
