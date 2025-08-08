from z3 import *
import json

def main():
    s = Solver()
    
    e = [Int('e%d' % i) for i in range(13)]
    city_map = {0: 'Prague', 1: 'Berlin', 2: 'Tallinn', 3: 'Stockholm'}
    
    for i in range(13):
        s.add(e[i] >= 0, e[i] <= 3)
    
    direct_flights = set()
    direct_flights.add((0, 2))  # Prague to Tallinn
    direct_flights.add((2, 0))  # Tallinn to Prague
    direct_flights.add((1, 2))  # Berlin to Tallinn
    direct_flights.add((2, 1))  # Tallinn to Berlin
    direct_flights.add((3, 2))  # Stockholm to Tallinn
    direct_flights.add((2, 3))  # Tallinn to Stockholm
    direct_flights.add((0, 3))  # Prague to Stockholm
    direct_flights.add((3, 0))  # Stockholm to Prague
    direct_flights.add((1, 3))  # Berlin to Stockholm
    direct_flights.add((3, 1))  # Stockholm to Berlin
    
    for i in range(1, 13):
        constraints = []
        for flight in direct_flights:
            a, b = flight
            constraints.append(And(e[i-1] == a, e[i] == b))
        s.add(Implies(e[i-1] != e[i], Or(constraints)))
    
    total_days = [0]*4
    for city in range(4):
        total = 0
        for i in range(1, 13):
            total += If(Or(e[i-1] == city, e[i] == city), 1, 0)
        total_days[city] = total
    
    s.add(total_days[0] == 2)  # Prague: 2 days
    s.add(total_days[1] == 3)  # Berlin: 3 days
    s.add(total_days[2] == 5)  # Tallinn: 5 days
    s.add(total_days[3] == 5)  # Stockholm: 5 days
    
    s.add(Or(e[5] == 1, e[6] == 1))  # Day 6 in Berlin
    s.add(e[7] == 1)  # Start of day 8 in Berlin
    s.add(e[8] == 2)  # End of day 8 in Tallinn
    for i in range(9, 13):
        s.add(e[i] == 2)  # End of days 9-12 in Tallinn
    
    if s.check() == sat:
        m = s.model()
        res = [m.evaluate(e_i).as_long() for e_i in e]
        states = res[:12]  # Start-of-day for days 1 to 12: e0 to e11
        itinerary = []
        current_city = states[0]
        start_day = 1
        for day in range(2, 13):  # day from 2 to 12
            if states[day-1] != current_city:
                if start_day == day-1:
                    day_range = f"Day {start_day}"
                else:
                    day_range = f"Day {start_day}-{day-1}"
                itinerary.append({'day_range': day_range, 'place': city_map[current_city]})
                current_city = states[day-1]
                start_day = day
        if start_day == 12:
            day_range = "Day 12"
        else:
            day_range = f"Day {start_day}-12"
        itinerary.append({'day_range': day_range, 'place': city_map[current_city]})
        result_dict = {"itinerary": itinerary}
        print(json.dumps(result_dict))
    else:
        print(json.dumps({"error": "No solution found"}))

if __name__ == "__main__":
    main()