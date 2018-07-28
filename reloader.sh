#!/bin/bash
render () {
    agda --latex AVL.lagda
    (
        cd latex || exit
        latexmk -silent -f -pdf AVL.tex || exit
    )
    osascript -e 'tell application "Skim"
	set opens to (get documents whose path contains "AVL.pdf")
  	if (count of opens) is 0 then
	  	open POSIX file "/Users/doisinkidney/Developer/agda-avl/latex/AVL.pdf"
   	else
	   	revert opens
    end if
end tell'
}
render
fswatch "AVL.lagda" | while read -r ; do
    echo "Changed"
    render
done
