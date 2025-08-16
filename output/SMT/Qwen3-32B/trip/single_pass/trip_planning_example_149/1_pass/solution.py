from z3 import *
import json

def main():
    # Define cities using Z3's EnumSort
    City, (London, Santorini, Istanbul) = EnumSort('City', ['London', 'Santorini', 'Istanbul'])
    days = 10
    day_city = [Const(f'day_{i+1}', City) for i in range(days)]  # 10 days

    s = Solver()

    # Conference constraints: Day 5 and Day 10 must be in Santorini
    s.add(day_city[4] == Santorini)  # Day 5
    s.add(day_city[9] == Santorini)  # Day 10

    # Flight constraints and transition count
    transitions = []
    for i in range(days - 1):  # 0 to 8 (days 1-9)
        current = day_city[i]
        next_day = day_city[i+1]
        # Only allow direct flights between (London ↔ Istanbul) and (London ↔ Santorini)
        s.add(Or(current == next_day,
                 And(current == London, next_day == Istanbul),
                 And(current == Istanbul, next_day == London),
                 And(current == London, next_day == Santorini),
                 And(current == Santorini, next_day == London)))
        # Track transitions (1 if different cities, 0 otherwise)
        transitions.append(If(current != next_day, 1, 0))

    # Ensure exactly 2 transitions (flights)
    s.add(Sum(transitions) == 2)

    # Count how many days each city is visited in the itinerary
    count_London = Sum([If(day_city[i] == London, 1, 0) for i in range(days)])
    count_Santorini = Sum([If(day_city[i] == Santorini, 1, 0) for i in range(days)])
    count_Istanbul = Sum([If(day_city[i] == Istanbul, 1, 0) for i in range(days)])

    # Count transitions into and out of each city
    transitions_leaving_London = Sum([If(And(day_city[i] == London, day_city[i+1] != London), 1, 0) for i in range(days - 1)])
    transitions_entering_London = Sum([If(And(day_city[i+1] == London, day_city[i] != London), 1, 0) for i in range(days - 1)])
    total_London = count_London + transitions_leaving_London + transitions_entering_London
    s.add(total_London == 3)

    transitions_leaving_Santorini = Sum([If(And(day_city[i] == Santorini, day_city[i+1] != Santorini), 1, 0) for i in range(days - 1)])
    transitions_entering_Santorini = Sum([If(And(day_city[i+1] == Santorini, day_city[i] != Santorini), 1, 0) for i in range(days - 1)])
    total_Santorini = count_Santorini + transitions_leaving_Santorini + transitions_entering_Santorini
    s.add(total_Santorini == 6)

    transitions_leaving_Istanbul = Sum([If(And(day_city[i] == Istanbul, day_city[i+1] != Istanbul), 1, 0) for i in range(days - 1)])
    transitions_entering_Istanbul = Sum([If(And(day_city[i+1] == Istanbul, day_city[i] != Istanbul), 1, 0) for i in range(days - 1)])
    total_Istanbul = count_Istanbul + transitions_leaving_Istanbul + transitions_entering_Istanbul
    s.add(total_Istanbul == 3)

    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(days):
            city_val = m.eval(day_city[i])
            if city_val == London:
                city_str = 'London'
            elif city_val == Santorini:
                city_str = 'Santorini'
            elif city_val == Istanbul:
                city_str = 'Istanbul'
            else:
                city_str = 'Unknown'
            itinerary.append({'day': i+1, 'city': city_str})
        result = {'itinerary': itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()