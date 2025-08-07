last_end_expr = city_end[6]  # Default case
   for i in range(5, -1, -1):
       last_end_expr = If(seq[6] == i, city_end[i], last_end_expr)
   s.add(last_end_expr == 17)