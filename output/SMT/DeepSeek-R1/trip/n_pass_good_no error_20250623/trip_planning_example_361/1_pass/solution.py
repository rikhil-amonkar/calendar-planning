from z3 import *
import json

def main():
    # Define the City datatype
    City = Datatype('City')
    City.declare('Paris')
    City.declare('Madrid')
    City.declare('Bucharest')
    City.declare('Seville')
    City = City.create()
    
    # Create constants for each city
    Paris = City.Paris
    Madrid = City.Madrid
    Bucharest = City.Bucharest
    Seville = City.Seville

    # Define the solver
    s = Solver()
    
    # Define the variables
    city2 = Const('city2', City)
    city3 = Const('city3', City)
    move2_day = Int('move2_day')
    
    # Constraints on move2_day: between 8 and 13 inclusive
    s.add(move2_day >= 8, move2_day <= 13)
    
    # city2 and city3 must be Paris and Seville, and different
    s.add(Or(city2 == Paris, city2 == Seville))
    s.add(Or(city3 == Paris, city3 == Seville))
    s.add(city2 != city3)
    
    # Constraints on stay durations
    # For city2: if it's Paris, stay is 6 days; if Seville, 3 days
    # The stay in city2 is from day7 to move2_day (inclusive), so duration = move2_day - 7 + 1
    s.add(
        If(city2 == Paris, 
           (move2_day - 7 + 1) == 6,
           (move2_day - 7 + 1) == 3)
    )
    
    # For city3: if it's Paris, stay is 6 days; if Seville, 3 days
    # The stay in city3 is from move2_day to day14 (inclusive), so duration = 14 - move2_day + 1
    s.add(
        If(city3 == Paris,
           (14 - move2_day + 1) == 6,
           (14 - move2_day + 1) == 3)
    )
    
    # Define direct_flight function
    direct_flight = Function('direct_flight', City, City, BoolSort())
    # Add known direct flights (symmetric)
    flights = [
        (Madrid, Paris), (Paris, Madrid),
        (Madrid, Seville), (Seville, Madrid),
        (Madrid, Bucharest), (Bucharest, Madrid),
        (Paris, Seville), (Seville, Paris),
        (Paris, Bucharest), (Bucharest, Paris)
    ]
    # Set direct_flight to True for known pairs, False otherwise (though not strictly needed)
    for c1, c2 in flights:
        s.add(direct_flight(c1, c2) == True)
    
    # Flight constraints
    s.add(direct_flight(Madrid, city2) == True)
    s.add(direct_flight(city2, city3) == True)
    s.add(direct_flight(city3, Bucharest) == True)
    
    # Check and get the model
    if s.check() == sat:
        m = s.model()
        city2_val = m[city2]
        city3_val = m[city3]
        move2_day_val = m[move2_day].as_long()  # Get the integer value
        
        # Convert city values to string names
        city2_name = str(city2_val)
        city3_name = str(city3_val)
        
        # Build itinerary
        itinerary = [
            {"day_range": "Day 1-7", "place": "Madrid"},
            {"day_range": "Day 7", "place": "Madrid"},
            {"day_range": "Day 7", "place": city2_name},
            {"day_range": "Day 7-{}".format(move2_day_val), "place": city2_name},
            {"day_range": "Day {}".format(move2_day_val), "place": city2_name},
            {"day_range": "Day {}".format(move2_day_val), "place": city3_name},
            {"day_range": "Day {}-14".format(move2_day_val), "place": city3_name},
            {"day_range": "Day 14", "place": city3_name},
            {"day_range": "Day 14", "place": "Bucharest"},
            {"day_range": "Day 14-15", "place": "Bucharest"}
        ]
        
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()