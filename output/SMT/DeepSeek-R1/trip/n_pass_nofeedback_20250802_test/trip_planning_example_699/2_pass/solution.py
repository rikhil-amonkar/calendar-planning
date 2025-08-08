from z3 import *

def main():
    # Create solver instance
    s = Solver()

    # Days of the trip (16 days, index 0 to 15 for Day1 to Day16)
    n_days = 16
    city = [Int('city_%d' % i) for i in range(n_days)]

    # City mapping: 0=London, 1=Hamburg, 2=Dublin, 3=Helsinki, 4=Reykjavik, 5=Mykonos
    city_names = {
        0: 'London',
        1: 'Hamburg',
        2: 'Dublin',
        3: 'Helsinki',
        4: 'Reykjavik',
        5: 'Mykonos'
    }

    # Constraint: Each city variable must be between 0 and 5
    for i in range(n_days):
        s.add(city[i] >= 0, city[i] <= 5)

    # Constraint: Start and end in London (city 0)
    s.add(city[0] == 0)
    s.add(city[15] == 0)

    # Define allowed flight connections (direct flights)
    allowed_pairs = [
        (0,1), (0,2), (0,4), (0,5),
        (1,0), (1,2), (1,3),
        (2,0), (2,1), (2,4),
        (3,1), (3,4),
        (4,0), (4,2), (4,3), (4,5),
        (5,0), (5,4)
    ]

    # Constraint: For consecutive days, either stay in the same city or fly directly
    for i in range(n_days - 1):
        c1 = city[i]
        c2 = city[i+1]
        # If moving to a different city, ensure there's a direct flight
        move_cond = Or([And(c1 == a, c2 == b) for (a, b) in allowed_pairs])
        s.add(Or(c1 == c2, move_cond))

    # Constraint: No more than 3 consecutive days in the same city
    for i in range(n_days - 3):
        s.add(Not(And(city[i] == city[i+1], city[i+1] == city[i+2], city[i+2] == city[i+3])))
    
    # Constraint: Visit each city at least once
    for c in range(6):
        s.add(Or([city[i] == c for i in range(n_days)]))

    # Check for a solution
    if s.check() == sat:
        m = s.model()
        # Extract the city sequence
        assignment = [m.evaluate(city[i]).as_long() for i in range(n_days)]
        # Group consecutive days in the same city
        itinerary = []
        start_index = 0
        current_city = assignment[0]
        for i in range(1, n_days):
            if assignment[i] != current_city:
                start_day = start_index + 1
                end_day = i
                if start_day == end_day:
                    day_range = f"Day {start_day}"
                else:
                    day_range = f"Day {start_day}-{end_day}"
                itinerary.append({'day_range': day_range, 'place': city_names[current_city]})
                start_index = i
                current_city = assignment[i]
        # Add the last block
        start_day = start_index + 1
        end_day = n_days
        if start_day == end_day:
            day_range = f"Day {start_day}"
        else:
            day_range = f"Day {start_day}-{end_day}"
        itinerary.append({'day_range': day_range, 'place': city_names[current_city]})
        
        # Output the itinerary
        print("Plan found:", {'itinerary': itinerary})
    else:
        print("No valid plan found.")

if __name__ == "__main__":
    main()