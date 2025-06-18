from z3 import *

def main():
    city_map = {
        'Salzburg': 0,
        'Venice': 1,
        'Bucharest': 2,
        'Brussels': 3,
        'Hamburg': 4,
        'Copenhagen': 5,
        'Nice': 6,
        'Zurich': 7,
        'Naples': 8
    }
    days = [2, 5, 4, 2, 4, 4, 3, 5, 4]
    
    connections = [
        "Zurich and Brussels", "Bucharest and Copenhagen", "Venice and Brussels", "Nice and Zurich",
        "Hamburg and Nice", "Zurich and Naples", "Hamburg and Bucharest", "Zurich and Copenhagen",
        "Bucharest and Brussels", "Hamburg and Brussels", "Venice and Naples", "Venice and Copenhagen",
        "Bucharest and Naples", "Hamburg and Copenhagen", "Venice and Zurich", "Nice and Brussels",
        "Hamburg and Venice", "Copenhagen and Naples", "Nice and Naples", "Hamburg and Zurich",
        "Salzburg and Hamburg", "Zurich and Bucharest", "Brussels and Naples", "Copenhagen and Brussels",
        "Venice and Nice", "Nice and Copenhagen"
    ]
    
    allowed_set = set()
    for conn in connections:
        parts = conn.split(' and ')
        c1 = city_map[parts[0]]
        c2 = city_map[parts[1]]
        allowed_set.add((c1, c2))
        allowed_set.add((c2, c1))
    
    s = Solver()
    
    order = [Int(f'order_{i}') for i in range(9)]
    for i in range(9):
        s.add(order[i] >= 0, order[i] < 9)
    s.add(Distinct(order))
    
    cumulative = [Int(f'cum_{i}') for i in range(9)]
    s.add(cumulative[0] == days[order[0]])
    for i in range(1, 9):
        s.add(cumulative[i] == cumulative[i-1] + days[order[i]])
    
    s.add(order[0] == city_map['Salzburg'])
    s.add(order[1] == city_map['Hamburg'])
    
    for i in range(8):
        cons_list = []
        for (a, b) in allowed_set:
            cons_list.append(And(order[i] == a, order[i+1] == b))
        s.add(Or(cons_list))
    
    def get_start_end(c):
        start_c = 0
        for pos in range(9):
            if pos == 0:
                term = If(order[pos] == c, 1, 0)
            else:
                term = If(order[pos] == c, cumulative[pos-1] - (pos-1), 0)
            start_c += term
        end_c = 0
        for pos in range(9):
            term = If(order[pos] == c, cumulative[pos] - pos, 0)
            end_c += term
        return (start_c, end_c)
    
    s_brussels, e_brussels = get_start_end(3)
    s.add(s_brussels <= 22, e_brussels >= 21)
    
    s_copenhagen, e_copenhagen = get_start_end(5)
    s.add(s_copenhagen <= 21, e_copenhagen >= 18)
    
    s_nice, e_nice = get_start_end(6)
    s.add(s_nice <= 11, e_nice >= 9)
    
    s_naples, e_naples = get_start_end(8)
    s.add(s_naples <= 25, e_naples >= 22)
    
    if s.check() == sat:
        m = s.model()
        order_val = [m.evaluate(order[i]).as_long() for i in range(9)]
        cum_val = [m.evaluate(cumulative[i]).as_long() for i in range(9)]
        
        inv_city_map = {v: k for k, v in city_map.items()}
        itinerary = []
        
        for i in range(9):
            city_idx = order_val[i]
            city_name = inv_city_map[city_idx]
            if i == 0:
                start_i = 1
            else:
                start_i = cum_val[i-1] - (i-1)
            end_i = cum_val[i] - i
            
            if start_i == end_i:
                day_range = f"Day {start_i}"
            else:
                day_range = f"Day {start_i}-{end_i}"
            itinerary.append({'day_range': day_range, 'place': city_name})
            
            if i < 8:
                itinerary.append({'day_range': f"Day {end_i}", 'place': city_name})
                next_city_idx = order_val[i+1]
                next_city_name = inv_city_map[next_city_idx]
                itinerary.append({'day_range': f"Day {end_i}", 'place': next_city_name})
        
        result = {'itinerary': itinerary}
        print(result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()