required_expr = required_days_by_index[0]
for i in range(1, 10):
    required_expr = If(city_idx == i, required_days_by_index[i], required_expr)