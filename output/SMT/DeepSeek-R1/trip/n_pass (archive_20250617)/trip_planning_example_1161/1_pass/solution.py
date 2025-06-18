from z3 import *

def main():
    # City indices
    oslo = 0
    krakow = 1
    vilnius = 2
    helsinki = 3
    dubrovnik = 4
    madrid = 5
    mykonos = 6
    paris = 7

    city_names = {
        oslo: "Oslo",
        krakow: "Krakow",
        vilnius: "Vilnius",
        helsinki: "Helsinki",
        dubrovnik: "Dubrovnik",
        madrid: "Madrid",
        mykonos: "Mykonos",
        paris: "Paris"
    }

    # Required days for each city
    days = {
        oslo: 2,
        krakow: 5,
        vilnius: 2,
        helsinki: 2,
        dubrovnik: 3,
        madrid: 5,
        mykonos: 4,
        paris: 2
    }

    # Flight connections as undirected edges
    edges = [
        (oslo, krakow),
        (oslo, paris),
        (paris, madrid),
        (helsinki, vilnius),
        (oslo, madrid),
        (oslo, helsinki),
        (helsinki, krakow),
        (dubrovnik, helsinki),
        (dubrovnik, madrid),
        (oslo, dubrovnik),
        (krakow, paris),
        (madrid, mykonos),
        (oslo, vilnius),
        (krakow, vilnius),
        (helsinki, paris),
        (vilnius, paris),
        (helsinki, madrid)
    ]
    
    # Make the flight_set symmetric (both directions)
    flight_set = set()
    for a, b in edges:
        flight_set.add((a, b))
        flight_set.add((b, a))
    flight_list = list(flight_set)

    s = Solver()

    # Order of cities (8 cities)
    order = [Int('order_%d' % i) for i in range(8)]
    # Fix the known parts of the sequence
    s.add(order[0] == oslo)
    s.add(order[1] == dubrovnik)
    s.add(order[6] == madrid)
    s.add(order[7] == mykonos)

    # The remaining positions (2,3,4,5) must be krakow, vilnius, helsinki, paris (distinct)
    remaining = [krakow, vilnius, helsinki, paris]
    for i in [2,3,4,5]:
        s.add(Or([order[i] == c for c in remaining]))
    s.add(Distinct(order))

    # Flight constraints between consecutive cities
    for i in range(7):
        a = order[i]
        b = order[i+1]
        cons = Or([And(a == edge[0], b == edge[1]) for edge in flight_list])
        s.add(cons)

    # Start and end days for each city
    start = [Int('start_%d' % i) for i in range(8)]
    end = [Int('end_%d' % i) for i in range(8)]

    # Fixed constraints for Oslo, Dubrovnik, Mykonos
    s.add(start[oslo] == 1)
    s.add(end[oslo] == 2)
    s.add(start[dubrovnik] == 2)
    s.add(end[dubrovnik] == 4)
    s.add(start[mykonos] == 15)
    s.add(end[mykonos] == 18)

    # Duration constraints for other cities
    for i in range(8):
        if i not in [oslo, dubrovnik, mykonos]:
            s.add(end[i] - start[i] + 1 == days[i])

    # The end of a city is the start of the next
    for i in range(7):
        s.add(end[order[i]] == start[order[i+1]])

    # Start and end days are within [1,18] and start <= end
    for i in range(8):
        s.add(start[i] >= 1)
        s.add(end[i] <= 18)
        s.add(start[i] <= end[i])

    # Check for a solution
    if s.check() == sat:
        m = s.model()
        order_vals = [m.evaluate(order[i]).as_long() for i in range(8)]
        start_vals = [m.evaluate(start[i]).as_long() for i in range(8)]
        end_vals = [m.evaluate(end[i]).as_long() for i in range(8)]
        
        # Print the travel plan
        print("Travel Plan:")
        for i in range(8):
            city_index = order_vals[i]
            city_name = city_names[city_index]
            s_day = start_vals[city_index]
            e_day = end_vals[city_index]
            print(f"{city_name}: from day {s_day} to day {e_day}")

        # Print the sequence
        print("\nSequence of cities:")
        seq_names = [city_names[order_vals[i]] for i in range(8)]
        print(" -> ".join(seq_names))

        # Print the daily schedule
        print("\nDaily Schedule:")
        for day in range(1, 19):
            cities_today = []
            for i in range(8):
                city_index = order_vals[i]
                s_day = start_vals[city_index]
                e_day = end_vals[city_index]
                if s_day <= day <= e_day:
                    cities_today.append(city_names[city_index])
            print(f"Day {day}: {', '.join(cities_today)}")
    else:
        print("No solution found")

if __name__ == '__main__':
    main()