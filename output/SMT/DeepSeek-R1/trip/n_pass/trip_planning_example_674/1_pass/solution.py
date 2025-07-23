from z3 import *
import json

def main():
    # Directed flight connections
    flights_set = [
        (0, 4), (4, 0),   # Helsinki <-> Reykjavik
        (5, 1), (1, 5),   # Budapest <-> Warsaw
        (2, 3), (3, 2),   # Madrid <-> Split
        (0, 3), (3, 0),   # Helsinki <-> Split
        (0, 2), (2, 0),   # Helsinki <-> Madrid
        (0, 5), (5, 0),   # Helsinki <-> Budapest
        (4, 1), (1, 4),   # Reykjavik <-> Warsaw
        (0, 1), (1, 0),   # Helsinki <-> Warsaw
        (2, 5), (5, 2),   # Madrid <-> Budapest
        (5, 4), (4, 5),   # Budapest <-> Reykjavik
        (2, 1), (1, 2),   # Madrid <-> Warsaw
        (1, 3), (3, 1),   # Warsaw <-> Split
        (4, 2)            # Reykjavik -> Madrid
    ]
    
    s = Solver()
    
    # Define variables for the stays (city indices)
    stay1 = Int('stay1')
    stay2 = Int('stay2')
    stay5 = Int('stay5')
    
    # Possible cities for the stays: Madrid (2), Split (3), Budapest (5)
    s.add(Or(stay1 == 2, stay1 == 3, stay1 == 5))
    s.add(Or(stay2 == 2, stay2 == 3, stay2 == 5))
    s.add(Or(stay5 == 2, stay5 == 3, stay5 == 5))
    s.add(Distinct(stay1, stay2, stay5))
    
    # Function to check flight existence
    def flight_exists(a, b):
        return Or([And(a == x, b == y) for (x, y) in flights_set])
    
    # Flight constraints
    s.add(flight_exists(0, stay1))           # Helsinki to stay1
    s.add(flight_exists(stay1, stay2))        # stay1 to stay2
    s.add(flight_exists(stay2, 4))            # stay2 to Reykjavik
    s.add(flight_exists(1, stay5))            # Warsaw to stay5
    
    if s.check() == sat:
        m = s.model()
        st1 = m[stay1].as_long()
        st2 = m[stay2].as_long()
        st5 = m[stay5].as_long()
        
        # Map indices to city names
        city_map = {
            0: "Helsinki",
            1: "Warsaw",
            2: "Madrid",
            3: "Split",
            4: "Reykjavik",
            5: "Budapest"
        }
        
        # Construct itinerary
        itinerary = []
        itinerary.append([city_map[0]])                      # Day 1
        itinerary.append([city_map[0], city_map[st1]])       # Day 2
        itinerary.append([city_map[st1]])                    # Day 3
        itinerary.append([city_map[st1]])                    # Day 4
        itinerary.append([city_map[st1], city_map[st2]])     # Day 5
        itinerary.append([city_map[st2]])                    # Day 6
        itinerary.append([city_map[st2]])                    # Day 7
        itinerary.append([city_map[st2], city_map[4]])       # Day 8
        itinerary.append([city_map[4], city_map[1]])         # Day 9
        itinerary.append([city_map[1]])                      # Day 10
        itinerary.append([city_map[1], city_map[st5]])       # Day 11
        itinerary.append([city_map[st5]])                    # Day 12
        itinerary.append([city_map[st5]])                    # Day 13
        itinerary.append([city_map[st5]])                    # Day 14
        
        result = {'itinerary': itinerary}
        print(json.dumps(result))
    else:
        print(json.dumps({"error": "No solution found"}))

if __name__ == "__main__":
    main()