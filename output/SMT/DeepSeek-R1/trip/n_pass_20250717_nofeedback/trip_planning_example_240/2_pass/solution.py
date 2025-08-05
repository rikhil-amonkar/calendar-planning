from z3 import *
import json

def main():
    # Define the cities and days
    cities = ['Prague', 'Berlin', 'Tallinn', 'Stockholm']
    days = list(range(1, 13))
    
    # Create a dictionary of variables: In[city][day]
    In = {}
    for city in cities:
        In[city] = {day: Bool(f"In_{city}_{day}") for day in days}
    
    # Initialize the solver
    s = Solver()
    
    # Fixed constraints for Tallinn: must be present on days 8-12
    for day in [8, 9, 10, 11, 12]:
        s.add(In['Tallinn'][day] == True)
    
    # Fixed constraints for Berlin: must be present on days 6 and 8
    s.add(In['Berlin'][6] == True)
    s.add(In['Berlin'][8] == True)
    
    # Total days constraints for each city
    s.add(Sum([If(In['Prague'][day], 1, 0) for day in days]) == 2)
    s.add(Sum([If(In['Berlin'][day], 1, 0) for day in days]) == 3)
    s.add(Sum([If(In['Tallinn'][day], 1, 0) for day in days]) == 5)
    s.add(Sum([If(In['Stockholm'][day], 1, 0) for day in days]) == 5)
    
    # Define allowed direct flight pairs
    allowed_flights = [
        "Berlin and Tallinn",
        "Prague and Tallinn",
        "Stockholm and Tallinn",
        "Prague and Stockholm",
        "Stockholm and Berlin"
    ]
    allowed_pairs = set()
    for flight in allowed_flights:
        parts = flight.split(' and ')
        sorted_pair = tuple(sorted(parts))
        allowed_pairs.add(sorted_pair)
    
    # Generate all possible city pairs
    all_pairs = []
    for i in range(len(cities)):
        for j in range(i+1, len(cities)):
            pair = tuple(sorted([cities[i], cities[j]]))
            all_pairs.append(pair)
    
    # Identify forbidden pairs (not in allowed_pairs)
    forbidden_pairs = [pair for pair in all_pairs if pair not in allowed_pairs]
    
    # Add constraints for forbidden pairs: they cannot be together on the same day
    for (A, B) in forbidden_pairs:
        for day in days:
            s.add(Not(And(In[A][day], In[B][day])))
    
    # Each day must have at least one city and at most two cities
    for day in days:
        cities_present = [In[city][day] for city in cities]
        s.add(Sum([If(c, 1, 0) for c in cities_present]) >= 1)
        s.add(Sum([If(c, 1, 0) for c in cities_present]) <= 2)
    
    # Check if the problem is satisfiable
    if s.check() == sat:
        model = s.model()
        itinerary_list = []
        for day in days:
            for city in cities:
                if is_true(model.eval(In[city][day])):
                    itinerary_list.append({"day": day, "place": city})
        result = {'itinerary': itinerary_list}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()