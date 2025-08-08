from z3 import *

def main():
    s = Solver()

    e0, e1, e2, e3, e4, e5 = Ints('e0 e1 e2 e3 e4 e5')
    city = [Int(f'city_{i}') for i in range(7)]

    cities = ["Seville", "Vilnius", "Santorini", "London", "Stuttgart", "Dublin", "Frankfurt"]
    req = [5, 3, 2, 2, 3, 3, 5]

    s.add(Distinct(city))
    for i in range(7):
        s.add(city[i] >= 0, city[i] < 7)

    s.add(Or(
        And(city[2] == 4, e1 == 7, e2 == 9),
        And(city[3] == 4, e2 == 7, e3 == 9),
        And(city[4] == 4, e3 == 7, e4 == 9),
        And(city[5] == 4, e4 == 7, e5 == 9)
    ))

    s.add(e0 >= 1, e0 <= 17)
    s.add(e1 >= e0, e1 <= 17)
    s.add(e2 >= e1, e2 <= 17)
    s.add(e3 >= e2, e3 <= 17)
    s.add(e4 >= e3, e4 <= 17)
    s.add(e5 >= e4, e5 <= 17)

    durations = [
        e0,
        e1 - e0 + 1,
        e2 - e1 + 1,
        e3 - e2 + 1,
        e4 - e3 + 1,
        e5 - e4 + 1,
        17 - e5 + 1
    ]

    for i in range(7):
        s.add(Or([And(city[i] == j, durations[i] == req[j]) for j in range(7)]))

    starts = [1, e0, e1, e2, e3, e4, e5]
    ends = [e0, e1, e2, e3, e4, e5, 17]

    for i in range(7):
        in_london = (city[i] == 3)
        cover9 = And(starts[i] <= 9, 9 <= ends[i])
        cover10 = And(starts[i] <= 10, 10 <= ends[i])
        s.add(If(in_london, Or(cover9, cover10), True))

    edges = [(6,5), (6,3), (3,5), (1,6), (6,4), (5,0), (3,2), (4,3), (2,5)]
    for i in range(6):
        cons = []
        for a, b in edges:
            cons.append(And(city[i] == a, city[i+1] == b))
            cons.append(And(city[i] == b, city[i+1] == a))
        s.add(Or(cons))

    if s.check() == sat:
        m = s.model()
        e0_val = m[e0].as_long()
        e1_val = m[e1].as_long()
        e2_val = m[e2].as_long()
        e3_val = m[e3].as_long()
        e4_val = m[e4].as_long()
        e5_val = m[e5].as_long()
        city_vals = [m[city[i]].as_long() for i in range(7)]

        starts = [1, e0_val, e1_val, e2_val, e3_val, e4_val, e5_val]
        ends = [e0_val, e1_val, e2_val, e3_val, e4_val, e5_val, 17]

        itinerary = []
        for day in range(1, 18):
            cities_list = []
            for seg in range(7):
                if starts[seg] <= day <= ends[seg]:
                    cities_list.append(cities[city_vals[seg]])
            itinerary.append({"day": day, "cities": cities_list})

        result = {'itinerary': itinerary}
        print(result)
    else:
        print("No solution found")

if __name__ == '__main__':
    main()