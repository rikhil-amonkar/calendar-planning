from z3 import *
import json

def main():
    city_names = ['Reykjavik', 'Riga', 'Oslo', 'Lyon', 'Dubrovnik', 'Madrid', 'Warsaw', 'London']
    req_days = [4, 2, 3, 5, 2, 2, 4, 3]
    city_index = {name: idx for idx, name in enumerate(city_names)}
    
    flights_list = [
        ('Warsaw', 'Reykjavik'),
        ('Oslo', 'Madrid'),
        ('Warsaw', 'Riga'),
        ('Lyon', 'London'),
        ('Madrid', 'London'),
        ('Warsaw', 'London'),
        ('Reykjavik', 'Madrid'),
        ('Warsaw', 'Oslo'),
        ('Oslo', 'Dubrovnik'),
        ('Oslo', 'Reykjavik'),
        ('Riga', 'Oslo'),
        ('Oslo', 'Lyon'),
        ('Oslo', 'London'),
        ('London', 'Reykjavik'),
        ('Warsaw', 'Madrid'),
        ('Madrid', 'Lyon'),
        ('Dubrovnik', 'Madrid')
    ]
    
    allowed_pairs = set()
    for a, b in flights_list:
        i = city_index[a]
        j = city_index[b]
        allowed_pairs.add((i, j))
        allowed_pairs.add((j, i))
    
    s = Solver()
    
    seq = [Int(f'seq_{i}') for i in range(8)]
    s.add(Distinct(seq))
    for i in range(8):
        s.add(seq[i] >= 0, seq[i] < 8)
    
    for k in range(7):
        constraints = []
        for pair in allowed_pairs:
            constraints.append(And(seq[k] == pair[0], seq[k+1] == pair[1]))
        s.add(Or(constraints))
    
    pos_riga = Int('pos_riga')
    s.add(Or([And(seq[i] == city_index['Riga'], pos_riga == i) for i in range(8)]))
    
    pos_dub = Int('pos_dub')
    s.add(Or([And(seq[i] == city_index['Dubrovnik'], pos_dub == i) for i in range(8)]))
    
    def req_minus1(i):
        return Sum([If(seq[i] == c, req_days[c] - 1, 0) for c in range(8)])
    
    cum_riga = Sum([If(i < pos_riga, req_minus1(i), 0) for i in range(8)])
    start_riga = 1 + cum_riga
    end_riga = start_riga + (req_days[city_index['Riga']] - 1)
    
    cum_dub = Sum([If(i < pos_dub, req_minus1(i), 0) for i in range(8)])
    start_dub = 1 + cum_dub
    end_dub = start_dub + (req_days[city_index['Dubrovnik']] - 1)
    
    s.add(start_riga <= 5, end_riga >= 4)
    s.add(start_dub <= 8, end_dub >= 7)
    
    if s.check() == sat:
        model = s.model()
        seq_val = [model.evaluate(seq[i]).as_long() for i in range(8)]
        
        start_days = [0] * 8
        end_days = [0] * 8
        start_days[0] = 1
        for i in range(8):
            city_idx = seq_val[i]
            dur = req_days[city_idx]
            end_days[i] = start_days[i] + dur - 1
            if i < 7:
                start_days[i+1] = end_days[i]
        
        itinerary = []
        for i in range(8):
            city = city_names[seq_val[i]]
            start = start_days[i]
            end = end_days[i]
            if start == end:
                day_str = f"Day {start}"
            else:
                day_str = f"Day {start}-{end}"
            itinerary.append({"day_range": day_str, "place": city})
            
            if i < 7:
                flight_day = end_days[i]
                itinerary.append({"day_range": f"Day {flight_day}", "place": city})
                next_city = city_names[seq_val[i+1]]
                itinerary.append({"day_range": f"Day {flight_day}", "place": next_city})
        
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()