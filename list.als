module list[Time]

open order[Time]

abstract sig Item_Condition {}

one sig Outside_List_Item extends Item_Condition {}

one sig List_Item extends Item_Condition {}

sig Item {
	condition: Item_Condition one -> Time,
	next: Item lone -> Time,
	prev: Item lone -> Time
}

one sig List {
	items: Item -> Time
}

fun list_items[t : Time] : set Item { condition.t.List_Item }
fun unallocated_items[t : Time] : set Item { condition.t.Outside_List_Item }
fun all_next[i: Item, t:Time] : set Item { i.^(next.t) }
fun all_prev[i: Item, t:Time] : set Item { i.^(prev.t) }
fun all_reachable[i: Item, t:Time] : set Item { i.all_next[t] + i.all_prev[t] }

pred list_valid[t : Time] { -- для задания начального состояния
	all i : t.list_items { -- работаем только с элементами списка
    some i.next.t implies i = i.next.t.prev.t -- если есть следующий, то его предыдущий - это текущий элемент
    some i.prev.t implies i = i.prev.t.next.t -- аналогично для предыдущих
  }
	all i : t.list_items | i not in i.all_reachable[t] -- нет циклов _в элементах списка_
  no (t.list_items & t.unallocated_items) -- элементы списка и свободные не пересекаются
  t.list_items = List.items.t -- все аллоцированные в списке 
  all i : t.list_items | i.all_reachable[t] + i = t.list_items -- все достижимые из каждого элемента - равны списку	
}

-- is_list_valid - не нужен, его функцию нормально может выполнять list_valid

pred is_list_valid[t : Time] { -- для проверок
	all i, j : Item | j = i.next.t iff i = j.prev.t --обратимость операции
	all i : Item | all t : Time | i not in i.^(next.t) -- нет циклов по next
	all i : Item | all t : Time | i not in i.^(prev.t) -- нет циклов по prev
	no i, j : Item | all t : Time | (j in i.^(next.t)) and (j in i .^(prev.t)) -- нет циклов
	
	all i : Item | (i.condition.t = Outside_List_Item) implies { -- свойства элементов вне списка
		#(i.next.t) = 0 -- размеры множеств лучше использовать только в run/check директивах, в предикатах
                    -- стараться никогда не закладываться на количественные свойства
                    -- no i.next.t
		#(i.prev.t) = 0
		all l : List | i not in l.items.t 
	}
	all i : Item | i.condition.t = List_Item implies
		one l : List | i in l.items.t --все элементы, помеченные List_Item, действительно в списке
	
	all l : List { --для элементов в списке 
		all disj i, j : Item | ((i in l.items.t) and (j in l.items.t)) implies
			((j in i.^(next.t)) or (j in i.^(prev.t))) -- достижимость каждого из каждого
		all disj i, j : Item | (i in l.items.t and j in i.next.t) implies j in l.items.t --next не может выводить из списка
		all disj i, j : Item | (i in l.items.t and j in i.prev.t) implies j in l.items.t --prev не может выводить из списка 
	}
}

pred items_the_same_except[now : Time, changed_items : set Item] {
	let past = now.prev {
		all it : Item - changed_items {
			it.condition.past = it.condition.now
			it.next.past = it.next.now
			it.prev.past = it.prev.now
		}
	}
}

pred empty[t : Time, l : List] {
	no it : Item | it in l.items.t
}

example: run {
	all t : Time {
    list_valid[t]
    #(t.list_items) >= 3 
  }
} for 6 but exactly 5 Item

assert list_validity {
	all t : Time | list_valid[t] implies is_list_valid[t]
}

validate: check list_validity for 5
