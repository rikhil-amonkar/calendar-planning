from z3 import *
import json

def main():
    city_names = ["Bucharest", "Tallinn", "Seville", "Stockholm", "Munich", "Milan"]
    d = [4, 2, 5, 5, 5, 2]  # durations for each city

    flight_edges_set = set()
    flight_edges_set.add((3, 5))  # Milan and Stockholm
    flight_edges_set.add((3, 4))  # Munich and Stockholm
    flight_edges_set.add((0, 4))  # Bucharest and Munich
    flight_edges_set.add((2, 4))  # Munich and Seville
    flight_edges_set.add((1, 3))  # Stockholm and Tallinn
    flight_edges_set.add((4, 5))  # Munich and Milan
    flight_edges_set.add((1, 4))  # Munich and Tallinn
    flight_edges_set.add((2, 5))  # Seville and Milan

    n = 6
    order = [Int('o%d' % i) for i in range(n)]
    s = Solver()

    for i in range(n):
        s.add(order[i] >= 0, order[i] < n)
    s.add(Distinct(order))

    start_pos = [0] * n
    start_pos[0] = 1
    for i in range(1, n):
        start_pos[i] = start_pos[i-1] + d[order[i-1]] - 1

    city_start = [0] * n
    for c in range(n):
        city_start[c] = If(order[0] == c, start_pos[0],
                        If(order[1] == c, start_pos[1],
                        If(order[2] == c, start_pos[2],
                        If(order[3] == c, start_pos[3],
                        If(order[4] == c, start_pos[4],
                        If(order[5] == c, start_pos[5], 0))))))

    s.add(city_start[0] <= 4)   # Bucharest must start by day 4
    s.add(city_start[4] <= 8)   # Munich must start by day 8
    s.add(And(city_start[2] >= 4, city_start[2] <= 12)) # Seville must start between day 4 and 12

    for i in range(5):
        c1 = order[i]
        c2 = order[i+1]
        conds = []
        for edge in flight_edges_set:
            a, b = edge
            conds.append(Or(And(c1 == a, c2 == b), And(c1 == b, c2 == a)))
        s.add(Or(conds))

    if s.check() == sat:
        m = s.model()
        order_val = [m.evaluate(order[i]).as_long() for i in range(n)]
        start_pos_val = [1] * n
        for i in range(1, n):
            prev_city = order_val[i-1]
            start_pos_val[i] = start_pos_val[i-1] + d[prev_city] - 1

        city_segment = [None] * n
        for i in range(n):
            city_index = order_val[i]
            s_val = start_pos_val[i]
            e_val = s_val + d[city_index] - 1
            city_segment[city_index] = (s_val, e_val)

        itinerary_list = []
        for day in range(1, 19):
            places = []
            for c in range(n):
                seg = city_segment[c]
                if seg[0] <= day <= seg[1]:
                    places.append(city_names[c])
            itinerary_list.append({"day": day, "place": places})
        
        result = {"itinerary": itinerary_list}
        print(json.dumps(result))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()