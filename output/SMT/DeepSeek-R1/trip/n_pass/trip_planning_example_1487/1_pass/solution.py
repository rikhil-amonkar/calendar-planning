from z3 import *
import json

def main():
    cities = ['Copenhagen', 'Geneva', 'Mykonos', 'Naples', 'Prague', 'Dubrovnik', 'Athens', 'Santorini', 'Brussels', 'Munich']
    durations = {
        'Copenhagen': 5,
        'Geneva': 3,
        'Mykonos': 2,
        'Naples': 4,
        'Prague': 2,
        'Dubrovnik': 3,
        'Athens': 4,
        'Santorini': 5,
        'Brussels': 4,
        'Munich': 5
    }
    
    non_mykonos = [c for c in cities if c != 'Mykonos']
    
    flight_connections_str = """Copenhagen and Dubrovnik, Brussels and Copenhagen, Prague and Geneva, Athens and Geneva, Naples and Dubrovnik, Athens and Dubrovnik, Geneva and Mykonos, Naples and Mykonos, Naples and Copenhagen, Munich and Mykonos, Naples and Athens, Prague and Athens, Santorini and Geneva, Athens and Santorini, Naples and Munich, Prague and Copenhagen, Brussels and Naples, Athens and Mykonos, Athens and Copenhagen, Naples and Geneva, Dubrovnik and Munich, Brussels and Munich, Prague and Brussels, Brussels and Athens, Athens and Munich, Geneva and Munich, Copenhagen and Munich, Brussels and Geneva, Copenhagen and Geneva, Prague and Munich, Copenhagen and Santorini, Naples and Santorini, Geneva and Dubrovnik"""
    
    flight_pairs = set()
    connections_list = [conn.strip() for conn in flight_connections_str.split(',')]
    for conn in connections_list:
        parts = conn.split(' and ')
        if len(parts) == 2:
            A, B = parts[0], parts[1]
            flight_pairs.add((A, B))
            flight_pairs.add((B, A))
    
    s = Solver()
    
    pos_vars = {}
    for city in cities:
        if city == 'Mykonos':
            pos_vars[city] = 9
        else:
            pos_vars[city] = Int(f'pos_{city}')
    
    s.add(Distinct([pos_vars[city] for city in cities]))
    for city in non_mykonos:
        s.add(pos_vars[city] >= 0)
        s.add(pos_vars[city] <= 8)
    
    start_day = {}
    end_day = {}
    for city in non_mykonos:
        sum_before = 0
        for d in non_mykonos:
            sum_before += If(pos_vars[d] < pos_vars[city], durations[d], 0)
        start_day[city] = 1 + sum_before - pos_vars[city]
        end_day[city] = start_day[city] + durations[city] - 1
    
    start_day['Mykonos'] = 27
    end_day['Mykonos'] = 28
    
    s.add(start_day['Copenhagen'] <= 15)
    s.add(end_day['Copenhagen'] >= 11)
    s.add(start_day['Naples'] <= 8)
    s.add(end_day['Naples'] >= 5)
    s.add(start_day['Athens'] <= 11)
    s.add(end_day['Athens'] >= 8)
    
    for k in range(9):
        or_conditions = []
        for (c1, c2) in flight_pairs:
            or_conditions.append(And(pos_vars[c1] == k, pos_vars[c2] == k+1))
        s.add(Or(or_conditions))
    
    for city in non_mykonos:
        s.add(start_day[city] >= 1)
        s.add(start_day[city] <= 28)
        s.add(end_day[city] >= 1)
        s.add(end_day[city] <= 28)
    
    if s.check() == sat:
        m = s.model()
        pos_vals = {}
        for city in cities:
            if city == 'Mykonos':
                pos_vals[city] = 9
            else:
                pos_vals[city] = m.eval(pos_vars[city]).as_long()
        
        sorted_cities = sorted(cities, key=lambda c: pos_vals[c])
        
        start_vals = {}
        end_vals = {}
        for city in non_mykonos:
            start_vals[city] = m.eval(start_day[city]).as_long()
            end_vals[city] = m.eval(end_day[city]).as_long()
        start_vals['Mykonos'] = 27
        end_vals['Mykonos'] = 28
        
        itinerary = []
        for idx, city in enumerate(sorted_cities):
            s_val = start_vals[city]
            e_val = end_vals[city]
            if s_val == e_val:
                day_str = f"Day {s_val}"
            else:
                day_str = f"Day {s_val}-{e_val}"
            itinerary.append({"day_range": day_str, "place": city})
            
            if idx < 9:
                next_city = sorted_cities[idx+1]
                itinerary.append({"day_range": f"Day {e_val}", "place": city})
                itinerary.append({"day_range": f"Day {e_val}", "place": next_city})
        
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()