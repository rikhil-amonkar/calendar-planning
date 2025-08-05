from z3 import *

def main():
    # City indices
    city_to_index = {
        "Riga": 0,
        "Frankfurt": 1,
        "Amsterdam": 2,
        "Vilnius": 3,
        "London": 4,
        "Stockholm": 5,
        "Bucharest": 6
    }
    index_to_city = {v: k for k, v in city_to_index.items()}
    req_array = [2, 3, 2, 5, 2, 3, 4]  # Riga, Frankfurt, Amsterdam, Vilnius, London, Stockholm, Bucharest

    # Direct flight edges (bidirectional)
    edges_list = [
        ("London", "Amsterdam"),
        ("Vilnius", "Frankfurt"),
        ("Riga", "Vilnius"),
        ("Riga", "Stockholm"),
        ("London", "Bucharest"),
        ("Amsterdam", "Stockholm"),
        ("Amsterdam", "Frankfurt"),
        ("Frankfurt", "Stockholm"),
        ("Bucharest", "Riga"),
        ("Amsterdam", "Riga"),
        ("Amsterdam", "Bucharest"),
        ("Riga", "Frankfurt"),
        ("Bucharest", "Frankfurt"),
        ("London", "Frankfurt"),
        ("London", "Stockholm"),
        ("Amsterdam", "Vilnius")
    ]
    directed_edges = []
    for u, v in edges_list:
        a = city_to_index[u]
        b = city_to_index[v]
        directed_edges.append((a, b))
        directed_edges.append((b, a))

    s = Solver()

    # P[0..6] are the cities in order
    P = [Int('P%d' % i) for i in range(7)]
    for i in range(7):
        s.add(And(P[i] >= 0, P[i] <= 6))
    s.add(Distinct(P))

    # Function to get requirement for a city index
    def city_req(city_idx):
        return If(city_idx == 0, 2,
                If(city_idx == 1, 3,
                If(city_idx == 2, 2,
                If(city_idx == 3, 5,
                If(city_idx == 4, 2,
                If(city_idx == 5, 3, 4))))))

    # Flight days F1 to F6
    F1 = Int('F1')
    s.add(F1 == city_req(P[0]))
    F2 = Int('F2')
    s.add(F2 == F1 + (city_req(P[1]) - 1))
    F3 = Int('F3')
    s.add(F3 == F2 + (city_req(P[2]) - 1))
    F4 = Int('F4')
    s.add(F4 == F3 + (city_req(P[3]) - 1))
    F5 = Int('F5')
    s.add(F5 == F4 + (city_req(P[4]) - 1))
    F6 = Int('F6')
    s.add(F6 == F5 + (city_req(P[5]) - 1))

    # Constraint for the last city
    s.add(16 - F6 == city_req(P[6]))

    # Flight days constraints: 1 <= F1 < F2 < F3 < F4 < F5 < F6 <= 15
    s.add(F1 >= 1, F1 <= 15)
    s.add(F2 > F1, F2 <= 15)
    s.add(F3 > F2, F3 <= 15)
    s.add(F4 > F3, F4 <= 15)
    s.add(F5 > F4, F5 <= 15)
    s.add(F6 > F5, F6 <= 15)

    # Amsterdam event: between day 2 and 3 (inclusive)
    ams_pos = Int('ams_pos')
    s.add(ams_pos == If(P[0] == 2, 0,
                If(P[1] == 2, 1,
                If(P[2] == 2, 2,
                If(P[3] == 2, 3,
                If(P[4] == 2, 4,
                If(P[5] == 2, 5, 6)))))))
    start_ams = If(ams_pos == 0, 1,
                If(ams_pos == 1, F1,
                If(ams_pos == 2, F2,
                If(ams_pos == 3, F3,
                If(ams_pos == 4, F4,
                If(ams_pos == 5, F5, F6))))))
    end_ams = If(ams_pos == 0, F1,
                If(ams_pos == 1, F2,
                If(ams_pos == 2, F3,
                If(ams_pos == 3, F4,
                If(ams_pos == 4, F5,
                If(ams_pos == 5, F6, 15))))))
    s.add(And(start_ams <= 3, end_ams >= 2))

    # Vilnius event: between day 7 and 11 (inclusive)
    vil_pos = Int('vil_pos')
    s.add(vil_pos == If(P[0] == 3, 0,
                If(P[1] == 3, 1,
                If(P[2] == 3, 2,
                If(P[3] == 3, 3,
                If(P[4] == 3, 4,
                If(P[5] == 3, 5, 6)))))))
    start_vil = If(vil_pos == 0, 1,
                If(vil_pos == 1, F1,
                If(vil_pos == 2, F2,
                If(vil_pos == 3, F3,
                If(vil_pos == 4, F4,
                If(vil_pos == 5, F5, F6))))))
    end_vil = If(vil_pos == 0, F1,
                If(vil_pos == 1, F2,
                If(vil_pos == 2, F3,
                If(vil_pos == 3, F4,
                If(vil_pos == 4, F5,
                If(vil_pos == 5, F6, 15))))))
    s.add(And(start_vil <= 11, end_vil >= 7))

    # Stockholm event: between day 13 and 15 (inclusive) -> we require at least one day >=13 and <=15
    stock_pos = Int('stock_pos')
    s.add(stock_pos == If(P[0] == 5, 0,
                If(P[1] == 5, 1,
                If(P[2] == 5, 2,
                If(P[3] == 5, 3,
                If(P[4] == 5, 4,
                If(P[5] == 5, 5, 6)))))))
    end_stock = If(stock_pos == 0, F1,
                If(stock_pos == 1, F2,
                If(stock_pos == 2, F3,
                If(stock_pos == 3, F4,
                If(stock_pos == 4, F5,
                If(stock_pos == 5, F6, 15))))))
    s.add(end_stock >= 13)

    # Flight constraints: consecutive cities must have a direct flight
    for i in range(6):
        constraints = []
        for a, b in directed_edges:
            constraints.append(And(P[i] == a, P[i+1] == b))
        s.add(Or(constraints))

    if s.check() == sat:
        model = s.model()
        P_val = [model.evaluate(P[i]).as_long() for i in range(7)]
        F1_val = model.evaluate(F1).as_long()
        F2_val = model.evaluate(F2).as_long()
        F3_val = model.evaluate(F3).as_long()
        F4_val = model.evaluate(F4).as_long()
        F5_val = model.evaluate(F5).as_long()
        F6_val = model.evaluate(F6).as_long()
        
        flight_days = [F1_val, F2_val, F3_val, F4_val, F5_val, F6_val]
        city_sequence = [index_to_city[idx] for idx in P_val]
        
        itinerary = []
        for d in range(1, 16):
            if d == F1_val:
                cities_today = [city_sequence[0], city_sequence[1]
            elif d == F2_val:
                cities_today = [city_sequence[1], city_sequence[2]
            elif d == F3_val:
                cities_today = [city_sequence[2], city_sequence[3]
            elif d == F4_val:
                cities_today = [city_sequence[3], city_sequence[4]
            elif d == F5_val:
                cities_today = [city_sequence[4], city_sequence[5]
            elif d == F6_val:
                cities_today = [city_sequence[5], city_sequence[6]]
            else:
                if d < F1_val:
                    cities_today = [city_sequence[0]]
                elif d < F2_val:
                    cities_today = [city_sequence[1]]
                elif d < F3_val:
                    cities_today = [city_sequence[2]]
                elif d < F4_val:
                    cities_today = [city_sequence[3]]
                elif d < F5_val:
                    cities_today = [city_sequence[4]]
                elif d < F6_val:
                    cities_today = [city_sequence[5]]
                else:
                    cities_today = [city_sequence[6]]
            for city in cities_today:
                itinerary.append({"day": d, "city": city})
        
        result = {"itinerary": itinerary}
        print(result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()