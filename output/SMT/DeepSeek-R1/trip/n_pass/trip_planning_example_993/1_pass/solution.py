import z3

# Map cities to integers
city_map = {
    'Riga': 0,
    'Frankfurt': 1,
    'Amsterdam': 2,
    'Vilnius': 3,
    'London': 4,
    'Stockholm': 5,
    'Bucharest': 6
}
reverse_city_map = {v: k for k, v in city_map.items()}

# Define directed flights (bidirectional pairs and one-way Riga->Vilnius)
pairs = [
    (4, 2),  # London - Amsterdam
    (3, 1),  # Vilnius - Frankfurt
    (0, 5),  # Riga - Stockholm
    (4, 6),  # London - Bucharest
    (2, 5),  # Amsterdam - Stockholm
    (2, 1),  # Amsterdam - Frankfurt
    (1, 5),  # Frankfurt - Stockholm
    (6, 0),  # Bucharest - Riga
    (2, 0),  # Amsterdam - Riga
    (2, 6),  # Amsterdam - Bucharest
    (0, 1),  # Riga - Frankfurt
    (6, 1),  # Bucharest - Frankfurt
    (4, 1),  # London - Frankfurt
    (4, 5),  # London - Stockholm
    (2, 3)   # Amsterdam - Vilnius
]
directed_edges_list = []
for (a, b) in pairs:
    directed_edges_list.append((a, b))
    directed_edges_list.append((b, a))
directed_edges_list.append((0, 3))  # Riga -> Vilnius (one-way)

# Create Z3 variables for each day (t0 to t15)
t = [z3.Int('t%d' % i) for i in range(16)]

s = z3.Solver()

# Domain constraint: each t[i] must be in [0, 6]
for i in range(16):
    s.add(t[i] >= 0, t[i] <= 6)

# Flight constraints for transitions between consecutive days
for i in range(15):  # from t[i] to t[i+1] for i in 0..14
    stay = (t[i] == t[i+1])
    flight_options = []
    for (a, b) in directed_edges_list:
        flight_options.append(z3.And(t[i] == a, t[i+1] == b))
    s.add(z3.Or(stay, z3.Or(flight_options)))

# Duration constraints for each city
days_per_city = [2, 3, 2, 5, 2, 3, 4]  # Riga, Frankfurt, Amsterdam, Vilnius, London, Stockholm, Bucharest
for c in range(7):
    total = 0
    for i in range(15):  # 15 days, each day uses t[i] and t[i+1]
        total += z3.If(z3.Or(t[i] == c, t[i+1] == c), 1, 0)
    s.add(total == days_per_city[c])

# Event constraints
# Amsterdam (c=2) between day 2 and 3: days 2 (t1, t2) and 3 (t2, t3)
s.add(z3.Or(t[1] == 2, t[2] == 2, t[3] == 2))
# Vilnius (c=3) between day 7 and 11: days 7 (t6, t7) to 11 (t10, t11)
s.add(z3.Or(t[6] == 3, t[7] == 3, t[8] == 3, t[9] == 3, t[10] == 3, t[11] == 3))
# Stockholm (c=5) between day 13 and 15: days 13 (t12, t13) to 15 (t14, t15)
s.add(z3.Or(t[12] == 5, t[13] == 5, t[14] == 5, t[15] == 5))

# Solve the problem
if s.check() == z3.sat:
    model = s.model()
    # Output the schedule
    for day in range(15):
        start_index = day
        end_index = day + 1
        start_val = model[t[start_index]].as_long()
        end_val = model[t[end_index]].as_long()
        start_city = reverse_city_map[start_val]
        end_city = reverse_city_map[end_val]
        if start_val == end_val:
            print(f"Day {day+1}: Stay in {start_city}")
        else:
            print(f"Day {day+1}: Fly from {start_city} to {end_city}")
else:
    print("No solution found")