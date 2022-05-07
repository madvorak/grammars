import tactic


lemma list_map_append_append {α β : Type} {x y z : list α} {f : α → β} :
  list.map f (x ++ y ++ z) = (list.map f x) ++ (list.map f y) ++ (list.map f z) :=
by simp only [list.map_append]

lemma list_filter_map_append_append {α β : Type} {x y z : list α} {f : α → option β} :
  list.filter_map f (x ++ y ++ z) = (list.filter_map f x) ++ (list.filter_map f y) ++ (list.filter_map f z) :=
by simp only [list.filter_map_append]

lemma list_drop_length_append {α : Type} {x y : list α} :
  list.drop x.length (x ++ y) = y :=
begin
  convert_to list.drop (x.length + 0) (x ++ y) = list.drop 0 y,
  apply list.drop_append,
end
