# Extract order and start days
order = [0] + [model[order_vars[i]].as_long() for i in range(1, 7)]
starts = [model[start_days[i]].as_long() for i in range(7)]