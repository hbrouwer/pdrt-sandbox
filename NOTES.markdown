Adding haddock docs to gh-pages
===============================

git checkout master
make clean

git checkout gh-pages
git rm -r dist/doc
git commit -m 'removed docs'
git push

git checkout master
make
make haddock

git checkout gh-pages
git add dist/doc
git commit -m 'updated docs'
git push
