from z3 import *
import json

def main():
    # Cities and their required days
    cities = ['Split', 'Bucharest', 'Riga', 'Lisbon', 'Tallinn', 'Lyon']
    days_arr = [3, 3, 5, 3, 4, 5]
    days_dict = {city: d for city, d in zip(cities, days_arr)}
    
    # Directed flights setup
    bidirectional_pairs = [
        ('Lisbon', 'Bucharest'),
        ('Berlin', 'Lisbon'),
        ('Bucharest', 'Riga'),
        ('Berlin', 'Riga'),
        ('Split', 'Lyon'),
        ('Lisbon', 'Riga'),
        ('Berlin', 'Split'),
        ('Lyon', 'Lisbon'),
        ('Berlin', 'Tallinn'),
        ('Lyon', 'Bucharest')
    ]
    directed_flights = set()
    for (A, B) in bidirectional_pairs:
        directed_flights.add((A, B))
        directed_flights.add((B, A))
    directed_flights.add(('Riga', 'Tallinn'))
    
    # Z3 variables for city order
    c0, c1, c2, c3, c4, c5 = Ints('c0 c1 c2 c3 c4 c5')
    s = Solver()
    s.add(Distinct(c0, c1, c2, c3, c4, c5))
    for var in [c0, c1, c2, c3, c4, c5]:
        s.add(var >= 0, var < 6)
    
    # Flight constraints: Berlin to first city
    allowed_first = []
    for idx in range(6):
        if ('Berlin', cities[idx]) in directed_flights:
            allowed_first.append(c0 == idx)
    s.add(Or(allowed_first))
    
    # Flight constraints between consecutive cities
    for i in range(5):
        allowed = []
        for idx_i in range(6):
            for idx_j in range(6):
                if idx_i == idx_j:
                    continue
                if (cities[idx_i], cities[idx_j]) in directed_flights:
                    if i == 0:
                        cond = And(c0 == idx_i, c1 == idx_j)
                    elif i == 1:
                        cond = And(c1 == idx_i, c2 == idx_j)
                    elif i == 2:
                        cond = And(c2 == idx_i, c3 == idx_j)
                    elif i == 3:
                        cond = And(c3 == idx_i, c4 == idx_j)
                    elif i == 4:
                        cond = And(c4 == idx_i, c5 == idx_j)
                    allowed.append(cond)
        s.add(Or(allowed))
    
    # Day variables for each position
    day_vars = [Int(f'day{i}') for i in range(6)]
    for i, var in enumerate(day_vars):
        s.add(var > 0)
        for idx in range(6):
            s.add(Implies(
                [c0 == idx, c1 == idx, c2 == idx, c3 == idx, c4 == idx, c5 == idx][i], 
                var == days_arr[idx]
            ))
    
    # Cumulative departure days
    cum0 = 5 + (day_vars[0] - 1)
    cum1 = cum0 + (day_vars[1] - 1)
    cum2 = cum1 + (day_vars[2] - 1)
    cum3 = cum2 + (day_vars[3] - 1)
    cum4 = cum3 + (day_vars[4] - 1)
    cum_list = [cum0, cum1, cum2, cum3, cum4]
    
    # Position variables for Bucharest and Lyon
    b_index = cities.index('Bucharest')
    l_index = cities.index('Lyon')
    pos_Bucharest = Int('pos_Bucharest')
    pos_Lyon = Int('pos_Lyon')
    s.add(pos_Bucharest >= 0, pos_Bucharest < 6)
    s.add(pos_Lyon >= 0, pos_Lyon < 6)
    for j in range(6):
        s.add(If(c0 == b_index, pos_Bucharest == 0, True))
        s.add(If(c1 == b_index, pos_Bucharest == 1, True))
        s.add(If(c2 == b_index, pos_Bucharest == 2, True))
        s.add(If(c3 == b_index, pos_Bucharest == 3, True))
        s.add(If(c4 == b_index, pos_Bucharest == 4, True))
        s.add(If(c5 == b_index, pos_Bucharest == 5, True))
        s.add(If(c0 == l_index, pos_Lyon == 0, True))
        s.add(If(c1 == l_index, pos_Lyon == 1, True))
        s.add(If(c2 == l_index, pos_Lyon == 2, True))
        s.add(If(c3 == l_index, pos_Lyon == 3, True))
        s.add(If(c4 == l_index, pos_Lyon == 4, True))
        s.add(If(c5 == l_index, pos_Lyon == 5, True))
    
    # Constraints for Bucharest and Lyon
    s.add(Or(
        And(pos_Bucharest == 1, cum0 >= 11, cum0 <= 15),
        And(pos_Bucharest == 2, cum1 >= 11, cum1 <= 15),
        And(pos_Bucharest == 3, cum2 >= 11, cum2 <= 15),
        And(pos_Bucharest == 4, cum3 >= 11, cum3 <= 15)
    ))
    s.add(Or(
        And(pos_Lyon == 0, 5 <= 11),  # 5 is the arrival day for position0
        And(pos_Lyon == 1, cum0 <= 11),
        And(pos_Lyon == 2, cum1 <= 11),
        And(pos_Lyon == 3, cum2 <= 11),
        And(pos_Lyon == 4, cum3 <= 11)
    ))
    
    # Solve the model
    if s.check() == sat:
        m = s.model()
        c0_val = m[c0].as_long()
        c1_val = m[c1].as_long()
        c2_val = m[c2].as_long()
        c3_val = m[c3].as_long()
        c4_val = m[c4].as_long()
        c5_val = m[c5].as_long()
        order = [c0_val, c1_val, c2_val, c3_val, c4_val, c5_val]
        cities_in_order = ['Berlin'] + [cities[idx] for idx in order]
        
        cum0_val = m.eval(cum0).as_long()
        cum1_val = m.eval(cum1).as_long()
        cum2_val = m.eval(cum2).as_long()
        cum3_val = m.eval(cum3).as_long()
        cum4_val = m.eval(cum4).as_long()
        breaks = [5, cum0_val, cum1_val, cum2_val, cum3_val, cum4_val]
        
        itinerary_list = []
        for day in range(1, 23):
            if day < 5:
                places = ['Berlin']
            elif day == 5:
                places = ['Berlin', cities_in_order[1]]
            else:
                if day in breaks:
                    idx = breaks.index(day)
                    places = [cities_in_order[idx], cities_in_order[idx+1]]
                else:
                    idx = 0
                    while idx < len(breaks) and breaks[idx] < day:
                        idx += 1
                    places = [cities_in_order[idx]]
            itinerary_list.append({"day": day, "place": places})
        
        result = {'itinerary': itinerary_list}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == '__main__':
    main()