from z3 import *

def main():
    cities = ['Paris', 'Warsaw', 'Krakow', 'Tallinn', 'Riga', 'Copenhagen', 'Helsinki', 'Oslo', 'Santorini', 'Lyon']
    days_list = [5, 2, 2, 2, 2, 5, 5, 5, 2, 4]
    days_dict = {city: days_list[i] for i, city in enumerate(cities)}
    city_to_index = {city: i for i, city in enumerate(cities)}
    index_to_city = {i: city for i, city in enumerate(cities)}
    
    santorini_idx = city_to_index['Santorini']
    krakow_idx = city_to_index['Krakow']
    riga_idx = city_to_index['Riga']
    paris_idx = city_to_index['Paris']
    helsinki_idx = city_to_index['Helsinki']
    
    edges_list = [
        (city_to_index['Warsaw'], city_to_index['Riga']),
        (city_to_index['Warsaw'], city_to_index['Tallinn']),
        (city_to_index['Copenhagen'], city_to_index['Helsinki']),
        (city_to_index['Lyon'], city_to_index['Paris']),
        (city_to_index['Copenhagen'], city_to_index['Warsaw']),
        (city_to_index['Lyon'], city_to_index['Oslo']),
        (city_to_index['Paris'], city_to_index['Oslo']),
        (city_to_index['Paris'], city_to_index['Riga']),
        (city_to_index['Krakow'], city_to_index['Helsinki']),
        (city_to_index['Paris'], city_to_index['Tallinn']),
        (city_to_index['Oslo'], city_to_index['Riga']),
        (city_to_index['Krakow'], city_to_index['Warsaw']),
        (city_to_index['Paris'], city_to_index['Helsinki']),
        (city_to_index['Copenhagen'], city_to_index['Santorini']),
        (city_to_index['Helsinki'], city_to_index['Warsaw']),
        (city_to_index['Helsinki'], city_to_index['Riga']),
        (city_to_index['Copenhagen'], city_to_index['Krakow']),
        (city_to_index['Copenhagen'], city_to_index['Riga']),
        (city_to_index['Paris'], city_to_index['Krakow']),
        (city_to_index['Copenhagen'], city_to_index['Oslo']),
        (city_to_index['Oslo'], city_to_index['Tallinn']),
        (city_to_index['Oslo'], city_to_index['Helsinki']),
        (city_to_index['Copenhagen'], city_to_index['Tallinn']),
        (city_to_index['Oslo'], city_to_index['Krakow']),
        (city_to_index['Riga'], city_to_index['Tallinn']),
        (city_to_index['Helsinki'], city_to_index['Tallinn']),
        (city_to_index['Paris'], city_to_index['Copenhagen']),
        (city_to_index['Paris'], city_to_index['Warsaw']),
        (city_to_index['Santorini'], city_to_index['Oslo']),
        (city_to_index['Oslo'], city_to_index['Warsaw'])
    ]
    allowed_edges = set()
    for u, v in edges_list:
        allowed_edges.add((min(u, v), max(u, v)))
    
    s = Solver()
    pos = [Int('pos_%d' % i) for i in range(10)]
    for i in range(10):
        s.add(pos[i] >= 0, pos[i] < 10)
    s.add(Distinct(pos))
    
    prefix_sum = [Int('prefix_sum_%d' % i) for i in range(11)]
    s.add(prefix_sum[0] == 0)
    days_arr = Array('days_arr', IntSort(), IntSort())
    for i in range(10):
        s.add(days_arr[i] == days_list[i])
    for i in range(10):
        s.add(prefix_sum[i+1] == prefix_sum[i] + days_arr[pos[i]])
    
    santorini_constraint = Or([And(pos[i] == santorini_idx, prefix_sum[i] == i + 10) for i in range(10)])
    s.add(santorini_constraint)
    
    krakow_constraint = Or([And(pos[i] == krakow_idx, prefix_sum[i] == i + 15) for i in range(10)])
    s.add(krakow_constraint)
    
    riga_constraint = Or([And(pos[i] == riga_idx, prefix_sum[i] == i + 21) for i in range(10)])
    s.add(riga_constraint)
    
    for i in range(9):
        u = pos[i]
        v = pos[i+1]
        edge_found = False
        for edge in allowed_edges:
            edge_found = Or(edge_found, And(u == edge[0], v == edge[1]), And(u == edge[1], v == edge[0]))
        s.add(edge_found)
    
    for i in range(10):
        s.add(Implies(pos[i] == paris_idx, (1 + prefix_sum[i] - i) <= 8))
    
    for i in range(10):
        s.add(Implies(pos[i] == helsinki_idx, And((1 + prefix_sum[i] - i) >= 14, (1 + prefix_sum[i] - i) <= 22)))
    
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(10):
            city_index = m.evaluate(pos[i]).as_long()
            city_name = index_to_city[city_index]
            start_i = 1 + m.evaluate(prefix_sum[i]).as_long() - i
            stay_days = days_list[city_index]
            end_i = start_i + stay_days - 1
            if start_i == end_i:
                day_range_str = "Day %d" % start_i
            else:
                day_range_str = "Day %d-%d" % (start_i, end_i)
            itinerary.append({"day_range": day_range_str, "place": city_name})
            if i < 9:
                next_city_index = m.evaluate(pos[i+1]).as_long()
                next_city_name = index_to_city[next_city_index]
                itinerary.append({"day_range": "Day %d" % end_i, "place": city_name})
                itinerary.append({"day_range": "Day %d" % end_i, "place": next_city_name})
        print({"itinerary": itinerary})
    else:
        print("No solution found")

if __name__ == "__main__":
    main()