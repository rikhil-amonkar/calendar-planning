from z3 import *

def main():
    city_names = ["Reykjavik", "Stockholm", "Porto", "Nice", "Venice", "Vienna", "Split", "Copenhagen"]
    city_index = {name: idx for idx, name in enumerate(city_names)}
    durations = [2, 2, 5, 3, 4, 3, 3, 2]
    
    flights_list = [
        ("Copenhagen", "Vienna"),
        ("Nice", "Stockholm"),
        ("Split", "Copenhagen"),
        ("Nice", "Reykjavik"),
        ("Nice", "Porto"),
        ("Reykjavik", "Vienna"),
        ("Stockholm", "Copenhagen"),
        ("Nice", "Venice"),
        ("Nice", "Vienna"),
        ("Reykjavik", "Copenhagen"),
        ("Nice", "Copenhagen"),
        ("Stockholm", "Vienna"),
        ("Venice", "Vienna"),
        ("Copenhagen", "Porto"),
        ("Reykjavik", "Stockholm"),
        ("Stockholm", "Split"),
        ("Split", "Vienna"),
        ("Copenhagen", "Venice"),
        ("Vienna", "Porto")
    ]
    
    allowed_list = []
    for a, b in flights_list:
        idx_a = city_index[a]
        idx_b = city_index[b]
        allowed_list.append((idx_a, idx_b))
        allowed_list.append((idx_b, idx_a))
    
    s = Solver()
    
    seq = [Int(f'seq_{i}') for i in range(8)]
    for i in range(8):
        s.add(seq[i] >= 0, seq[i] < 8)
    s.add(Distinct(seq))
    
    duration_array = Array('durations', IntSort(), IntSort())
    for j in range(8):
        s.add(duration_array[j] == durations[j])
    
    cumul = [Int(f'cumul_{i}') for i in range(8)]
    s.add(cumul[0] == 1)
    for i in range(1, 8):
        s.add(cumul[i] == cumul[i-1] + (duration_array[seq[i-1]] - 1))
    
    total_end = cumul[7] + (duration_array[seq[7]] - 1)
    s.add(total_end <= 17)
    
    reykjavik_idx = city_index["Reykjavik"]
    stockholm_idx = city_index["Stockholm"]
    vienna_idx = city_index["Vienna"]
    porto_idx = city_index["Porto"]
    
    start_reykjavik = Int('start_reykjavik')
    s.add(Or([And(seq[k] == reykjavik_idx, start_reykjavik == cumul[k]) for k in range(8)]))
    s.add(And(start_reykjavik >= 2, start_reykjavik <= 4))
    
    start_stockholm = Int('start_stockholm')
    s.add(Or([And(seq[k] == stockholm_idx, start_stockholm == cumul[k]) for k in range(8)]))
    s.add(And(start_stockholm >= 3, start_stockholm <= 5))
    
    start_vienna = Int('start_vienna')
    s.add(Or([And(seq[k] == vienna_idx, start_vienna == cumul[k]) for k in range(8)]))
    s.add(And(start_vienna >= 9, start_vienna <= 13))
    
    start_porto = Int('start_porto')
    s.add(Or([And(seq[k] == porto_idx, start_porto == cumul[k]) for k in range(8)]))
    s.add(And(start_porto >= 9, start_porto <= 13))
    
    for i in range(7):
        conds = []
        for (a, b) in allowed_list:
            conds.append(And(seq[i] == a, seq[i+1] == b))
        s.add(Or(conds))
    
    if s.check() == sat:
        model = s.model()
        seq_val = [model.evaluate(seq[i]).as_long() for i in range(8)]
        cumul_val = [model.evaluate(cumul[i]).as_long() for i in range(8)]
        
        itinerary = []
        for k in range(8):
            city_idx = seq_val[k]
            city_name = city_names[city_idx]
            start_day = cumul_val[k]
            end_day = start_day + durations[city_idx] - 1
            itinerary.append({
                "day_range": f"Day {start_day}-{end_day}",
                "place": city_name
            })
            if k < 7:
                itinerary.append({
                    "day_range": f"Day {end_day}",
                    "place": city_name
                })
                next_city_idx = seq_val[k+1]
                next_city_name = city_names[next_city_idx]
                itinerary.append({
                    "day_range": f"Day {end_day}",
                    "place": next_city_name
                })
        
        output = {"itinerary": itinerary}
        print(output)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()