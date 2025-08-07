from z3 import *

def main():
    # Define the City enum
    City, (R, I, E, O, S, B) = EnumSort('City', [
        'Reykjavik',
        'Istanbul',
        'Edinburgh',
        'Oslo',
        'Stuttgart',
        'Bucharest'
    ])
    
    # Create variables for each day (where we sleep at night)
    c = [Const('c_%d' % i, City) for i in range(1, 20)]
    
    s = Solver()
    
    # Define allowed flights (direct flights)
    allowed_flights = [
        (R, S),  # Reykjavik -> Stuttgart (only one way)
        (B, O), (O, B),  # Bucharest <-> Oslo
        (I, O), (O, I),  # Istanbul <-> Oslo
        (B, I), (I, B),  # Bucharest <-> Istanbul
        (S, E), (E, S),  # Stuttgart <-> Edinburgh
        (I, E), (E, I),  # Istanbul <-> Edinburgh
        (O, R), (R, O),  # Oslo <-> Reykjavik
        (I, S), (S, I),  # Istanbul <-> Stuttgart
        (O, E), (E, O)   # Oslo <-> Edinburgh
    ]
    
    # Constraint: consecutive days must be either the same city or connected by a direct flight
    for i in range(0, 18):
        current_city = c[i]
        next_city = c[i+1]
        s.add(If(current_city == next_city,
                 True,
                 Or([And(current_city == fr, next_city == to) for (fr, to) in allowed_flights])
                ))
    
    # Function to compute total days in a city
    def total_days(city):
        # Day 1: if we are in the city at the end (sleep there), then count 1
        total = If(c[0] == city, 1, 0)
        # Days 2 to 19: count 1 if either the start (previous sleep city) or the end (current sleep city) is the target city
        for i in range(1, 19):
            cond = Or(c[i-1] == city, c[i] == city)
            total = total + If(cond, 1, 0)
        return total
    
    # Add constraints for total days in each city
    s.add(total_days(R) == 5)  # Reykjavik
    s.add(total_days(I) == 4)  # Istanbul
    s.add(total_days(E) == 5)  # Edinburgh
    s.add(total_days(O) == 2)  # Oslo
    s.add(total_days(S) == 3)  # Stuttgart
    s.add(total_days(B) == 5)  # Bucharest
    
    # Helper function: check if in a city on a specific day
    def in_city(day, city):
        if day == 1:
            return c[0] == city
        else:
            return Or(c[day-2] == city, c[day-1] == city)  # day index: day-1 for c array, and previous day is day-2
    
    # Istanbul must be visited between days 5 and 8 (inclusive)
    s.add(Or(in_city(5, I), in_city(6, I), in_city(7, I), in_city(8, I)))
    
    # Oslo must be visited between days 8 and 9 (inclusive)
    s.add(Or(in_city(8, O), in_city(9, O)))
    
    # Check for a solution
    if s.check() == sat:
        model = s.model()
        itinerary_list = []
        for day in range(1, 20):
            city_val = model.evaluate(c[day-1])
            city_name = str(city_val)
            itinerary_list.append({"day": day, "place": city_name})
        
        # Format the output as JSON
        result = {
            "itinerary": itinerary_list
        }
        print(result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()