# Prague must be visited at least once during days 5-9 (0-based 4-8)
prague_days = [start_city[x] == city_to_idx['Prague'] for x in range(4, 9)]
s.add(z3.Or(prague_days))

# Split must be visited at least once during days 11-13 (0-based 10-12)
split_days = [start_city[x] == city_to_idx['Split'] for x in range(10, 13)]
s.add(z3.Or(split_days))

# Stockholm must be visited at least once during days 16-17 (0-based 15-16)
stockholm_days = [start_city[x] == city_to_idx['Stockholm'] for x in range(15, 17)]
s.add(z3.Or(stockholm_days))

# Vienna has at least one day in 1-5 (0-based 0-4)
vienna_days = [start_city[x] == city_to_idx['Vienna'] for x in range(5)]
s.add(z3.Or(vienna_days))

# Riga has at least one day in 15-16 (0-based 14-15)
riga_days = [start_city[x] == city_to_idx['Riga'] for x in range(14, 16)]
s.add(z3.Or(riga_days))