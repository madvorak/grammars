import tactic


lemma list_map_append_append {α β : Type} {x y z : list α} {f : α → β} :
  list.map f (x ++ y ++ z) = (list.map f x) ++ (list.map f y) ++ (list.map f z) :=
by rw [ list.map_append, list.map_append ]

lemma list_filter_map_append_append {α β : Type} {x y z : list α} {f : α → option β} :
  list.filter_map f (x ++ y ++ z) = (list.filter_map f x) ++ (list.filter_map f y) ++ (list.filter_map f z) :=
by rw [ list.filter_map_append, list.filter_map_append ]

lemma list_reverse_append_append {α : Type} {x y z : list α} :
  list.reverse (x ++ y ++ z) = z.reverse ++ y.reverse ++ x.reverse :=
by rw [ list.reverse_append, list.reverse_append, list.append_assoc ]
