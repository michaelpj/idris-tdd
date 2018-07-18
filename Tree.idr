module Tree

data Tree elem = Empty
               | Node (Tree elem) elem (Tree elem)
%name Tree tree, tree1

insert: Ord elem => elem -> Tree elem -> Tree elem
insert x Empty = Node Empty x Empty
insert x orig@(Node l y r) = case compare x y of
                             LT => Node (insert x l) y r
                             EQ => orig
                             GT => Node l y (insert x r)

listToTree: Ord a => List a -> Tree a
listToTree = foldr insert Empty

treeToList: Tree a -> List a
treeToList Empty = []
treeToList (Node l x r) = (treeToList l) ++ [x] ++ (treeToList r)


