s.add(Implies(
    current_city == city_map[city],
    Or(next_city == city_map[city], Or([next_city == n for n in neighbor_indices]))
))