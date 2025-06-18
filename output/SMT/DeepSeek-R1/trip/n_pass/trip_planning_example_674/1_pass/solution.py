from z3 import *
import json

def main():
    cities = ['Helsinki', 'Warsaw', 'Madrid', 'Split', 'Reykjavik', 'Budapest']
    days_arr = [2, 3, 4, 4, 2, 4]
    n = 6

    edges = [
        (0, 4), (4, 0),
        (5, 1), (1, 5),
        (2, 3), (3, 2),
        (0, 3), (3, 0),
        (0, 2), (2, 0),
        (0, 5), (5, 0),
        (4, 1), (1, 4),
        (0, 1), (1, 0),
        (2, 5), (5, 2),
        (5, 4), (4, 5),
        (2, 1), (1, 2),
        (1, 3), (3, 1),
        (4, 2)
    ]

    s = Solver()

    order = [Int('order_%d' % i) for i in range(n)]
    for i in range(n):
        s.add(order[i] >= 0)
        s.add(order[i] < n)
    s.add(Distinct(order))

    for i in range(5):
        constraints = []
        for u, v in edges:
            constraints.append(And(order[i] == u, order[i+1] == v))
        s.add(Or(constraints))

    def get_days(city_var):
        return If(city_var == 0, 2,
               If(city_var == 1, 3,
               If(city_var == 2, 4,
               If(city_var == 3, 4,
               If(city_var == 4, 2,
               If(city_var == 5, 4, 0))))))

    prefix_expr = [0] * (n+1)
    prefix_expr[0] = 0
    for i in range(1, n+1):
        city_index = order[i-1]
        d = get_days(city_index)
        prefix_expr[i] = prefix_expr[i-1] + d

    for k in range(n):
        city_k = order[k]
        s.add(If(city_k == 0, prefix_expr[k] - k <= 1, True))
        s.add(If(city_k == 4, 
                 And(prefix_expr[k] - k <= 8, prefix_expr[k+1] - k >= 8), 
                 True))
        s.add(If(city_k == 1,
                 And(prefix_expr[k] - k <= 10, prefix_expr[k+1] - k >= 9),
                 True))

    if s.check() == sat:
        m = s.model()
        order_vals = [m.evaluate(order[i]).as_long() for i in range(n)]
        prefix_num = [0] * (n+1)
        for i in range(1, n+1):
            city_idx = order_vals[i-1]
            prefix_num[i] = prefix_num[i-1] + days_arr[city_idx]

        itinerary = []
        for k in range(n):
            city_idx = order_vals[k]
            city_name = cities[city_idx]
            s_k = 1 + prefix_num[k] - k
            e_k = prefix_num[k+1] - k
            itinerary.append({'day_range': f'Day {s_k}-{e_k}', 'place': city_name})
            if k < n-1:
                next_city_idx = order_vals[k+1]
                next_city = cities[next_city_idx]
                itinerary.append({'day_range': f'Day {e_k}', 'place': city_name})
                itinerary.append({'day_range': f'Day {e_k}', 'place': next_city})

        result = {'itinerary': itinerary}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()