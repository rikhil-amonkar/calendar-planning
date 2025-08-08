#!/usr/bin/env python3
import json
import itertools

def main():
    # Input constraints
    total_days = 17
    durations = {
        "Rome": 4,
        "Mykonos": 3,
        "Nice": 3,
        "Riga": 3,
        "Bucharest": 4,
        "Munich": 4,
        "Krakow": 2
    }
    # Event constraints (to be checked later):
    # - Conference in Rome on day 1 and day 4 → Rome must be visited at the start covering day 1 and 4.
    # - Wedding in Mykonos between day 4 and day 6 → Mykonos visit must overlap with [4,6].
    # - Annual show in Krakow from day 16 to day 17 → Krakow must be visited at the end covering days 16–17.
    
    # Define the list of cities (7 European cities)
    cities = ["Rome", "Mykonos", "Nice", "Riga", "Bucharest", "Munich", "Krakow"]
    
    # Define direct flight connections.
    # For flights stated as "X and Y", we assume bidirectional connectivity.
    # For flights stated as "from X to Y", we add only a directional edge.
    flight_edges = [
        ("Nice", "Riga"),           # bidirectional
        ("Bucharest", "Munich"),     # bidirectional
        ("Mykonos", "Munich"),       # bidirectional
        ("Riga", "Bucharest"),       # bidirectional
        ("Rome", "Nice"),            # bidirectional
        ("Rome", "Munich"),          # bidirectional
        ("Mykonos", "Nice"),         # bidirectional
        ("Rome", "Mykonos"),         # bidirectional
        ("Munich", "Krakow"),        # bidirectional
        ("Rome", "Bucharest"),       # bidirectional
        ("Nice", "Munich"),          # bidirectional
        ("Riga", "Munich"),          # directional: from Riga to Munich
        ("Rome", "Riga")             # directional: from Rome to Riga
    ]
    
    # Build flight graph as a dictionary: key is the departure city, value is a set of reachable cities.
    flight_graph = {city: set() for city in cities}
    # The first 11 edges are bidirectional.
    for i, (a, b) in enumerate(flight_edges):
        if i < 11: 
            flight_graph[a].add(b)
            flight_graph[b].add(a)
        else:
            # directional edge: only add from a to b.
            flight_graph[a].add(b)
    
    # We know the itinerary must use exactly 6 flights because:
    # Sum of required days = 4+3+3+3+4+4+2 = 23 and each flight day is counted twice.
    # So 23 - (number of flights) = 17  → number of flights = 6.
    # Also, by the event constraints, Rome must be the first city and Krakow the last.
    
    # Fix Rome as the first city and Krakow as the last.
    middle_cities = [city for city in cities if city not in ["Rome", "Krakow"]]
    
    valid_itinerary = None
    # Try all orders (permutations) of the middle cities.
    for perm in itertools.permutations(middle_cities):
        order = ["Rome"] + list(perm) + ["Krakow"]
        # Check that there is a valid direct flight between every consecutive pair.
        flight_valid = True
        for i in range(len(order) - 1):
            if order[i+1] not in flight_graph[order[i]]:
                flight_valid = False
                break
        if not flight_valid:
            continue
        
        # Calculate the day ranges for each city.
        schedule = []
        current_day = 1
        for city in order:
            start_day = current_day
            end_day = start_day + durations[city] - 1
            schedule.append({"city": city, "start": start_day, "end": end_day})
            # If flying, the flight takes place on the departure day (overlap)
            if city != order[-1]:
                current_day = end_day
        
        # Check if the final day equals total_days.
        if schedule[-1]["end"] != total_days:
            continue
        
        # Check event constraints:
        # Conference in Rome on Day 1 and Day 4 (Rome must be the first city and cover day 1 to day 4)
        rome_sched = schedule[0]
        if rome_sched["start"] > 1 or rome_sched["end"] < 4:
            continue
        
        # Wedding in Mykonos between Day 4 and Day 6.
        mykonos_sched = next((s for s in schedule if s["city"] == "Mykonos"), None)
        if mykonos_sched is None or (mykonos_sched["start"] > 6 or mykonos_sched["end"] < 4):
            continue
        
        # Annual show in Krakow on Day 16 to Day 17.
        krakow_sched = schedule[-1]
        if krakow_sched["city"] != "Krakow" or krakow_sched["start"] > 16 or krakow_sched["end"] < 17:
            continue
        
        # If all constraints are satisfied, we found a valid itinerary.
        valid_itinerary = schedule
        break
    
    # Prepare output in JSON format.
    if valid_itinerary:
        output_itinerary = []
        for seg in valid_itinerary:
            day_range_str = f"Day {seg['start']}-{seg['end']}"
            output_itinerary.append({"day_range": day_range_str, "place": seg["city"]})
        result = {"itinerary": output_itinerary}
    else:
        result = {"itinerary": []}
    
    print(json.dumps(result))

if __name__ == "__main__":
    main()