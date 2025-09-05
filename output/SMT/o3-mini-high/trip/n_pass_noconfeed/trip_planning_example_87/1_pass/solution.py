from z3 import *
import json

def main():
    # Define the enumeration for cities.
    City, (Riga, Amsterdam, Mykonos) = EnumSort('City', ['Riga', 'Amsterdam', 'Mykonos'])
    
    # Total number of days is 7. We'll index them 0..6, corresponding to Day 1 to Day 7.
    # For each day, we assign a city.
    cities = [Const(f"city_{i}", City) for i in range(7)]
    
    # For days 2 to 7 (indices 1..6) we decide if a flight is taken.
    # flight[i] means: on Day (i+1) a flight is taken from cities[i-1] (departure) to cities[i] (arrival).
    # If flight[i] is False then we must have cities[i] == cities[i-1] (i.e., no change in city).
    flights = [None]  # Placeholder for day 1 (index 0) where no flight occurs.
    for i in range(1, 7):
        flights.append(Bool(f"flight_{i}"))
        
    s = Solver()
    
    # Exactly 2 flight days must occur (thus 2 flight transitions).
    s.add(Sum([If(flights[i], 1, 0) for i in range(1, 7)]) == 2)
    
    # For each day from Day 2 to Day 7 (indices 1..6),
    # if a flight is taken then the transition must be a direct flight between the two cities.
    # Allowed direct flights (bidirectional) are: Amsterdam <-> Mykonos and Riga <-> Amsterdam.
    for i in range(1, 7):
        allowed_transition = Or(
            And(cities[i-1] == Amsterdam, cities[i] == Mykonos),
            And(cities[i-1] == Mykonos, cities[i] == Amsterdam),
            And(cities[i-1] == Riga, cities[i] == Amsterdam),
            And(cities[i-1] == Amsterdam, cities[i] == Riga)
        )
        s.add(If(flights[i], allowed_transition, cities[i] == cities[i-1]))
        
    # Relatives in Riga must be visited between Day 1 and Day 2.
    # Since on Day 1 the traveler is in cities[0] and on Day 2, if a flight is taken, both cities[0] and cities[1] count,
    # we require that either cities[0] or cities[1] is Riga.
    s.add(Or(cities[0] == Riga, cities[1] == Riga))
    
    # Define a helper to compute the total "days" counted in a particular city.
    # Note: If a flight happens on a day, then that day contributes to both the departure and arrival cities.
    def city_presence(city_const):
        count = If(cities[0] == city_const, 1, 0)
        for i in range(1, 7):
            count += If(flights[i],
                        (If(cities[i-1] == city_const, 1, 0) + If(cities[i] == city_const, 1, 0)),
                        If(cities[i] == city_const, 1, 0))
        return count

    count_Riga   = city_presence(Riga)
    count_Amsterdam = city_presence(Amsterdam)
    count_Mykonos   = city_presence(Mykonos)
    
    # Constrain the required total days in each city.
    s.add(count_Riga == 2)
    s.add(count_Amsterdam == 2)
    s.add(count_Mykonos == 5)
    
    if s.check() == sat:
        m = s.model()
        
        # Determine the flight days (human day numbers). 
        # flights[1] corresponds to Day 2, flights[2] to Day 3, and so on.
        flight_days = []
        for i in range(1, 7):
            if m.evaluate(flights[i]):
                # Human day number is (i + 1)
                flight_days.append(i + 1)
                
        # Build itinerary segments.
        # The idea is to segment the trip at flight days.
        # If a flight occurs on Day X, then that day counts for both the previous and next segment.
        segments = []
        start_day = 1
        # For each flight day, create a segment from start_day to that flight day.
        for fd in flight_days:
            # The segment's place is determined by the city at the starting day (indexed start_day-1)
            segments.append({
                "day_range": f"Day {start_day}-{fd}",
                "place": str(m.evaluate(cities[start_day - 1]))
            })
            start_day = fd
        # Add the final segment from the last flight day to Day 7.
        segments.append({
            "day_range": f"Day {start_day}-7",
            "place": str(m.evaluate(cities[start_day - 1]))
        })
        
        output = {"itinerary": segments}
        print(json.dumps(output))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()