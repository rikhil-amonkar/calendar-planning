#!/usr/bin/env python3
import json

def main():
    # Input trip constraints
    total_days = 12
    # Planned days in each city (including overlap flight days)
    planned_days = {
        "Dublin": 2,   # must be visited for 2 days
        "Riga": 5,     # must be visited for 5 days
        "Vilnius": 7   # must be visited for 7 days
    }
    
    # Define the available direct flights.
    # "Dublin and Riga" means there is a direct flight linking them (bidirectional).
    # "From Riga to Vilnius" is a one‐way direct flight.
    direct_flights = {
        "Dublin": ["Riga"],
        "Riga": ["Dublin", "Vilnius"],
        "Vilnius": []  # No direct flight from Vilnius to any other city based on given info.
    }
    
    # For 3 cities with overlaps on flight days, the only ordering that satisfies the flight routes is:
    # Dublin -> Riga -> Vilnius.
    itinerary_order = ["Dublin", "Riga", "Vilnius"]
    
    # Validate flight connectivity for the chosen itinerary order.
    valid_itinerary = True
    for i in range(len(itinerary_order) - 1):
        current_city = itinerary_order[i]
        next_city = itinerary_order[i + 1]
        if next_city not in direct_flights.get(current_city, []):
            valid_itinerary = False
            break

    # Based on the overlapping rule:
    # If you fly from city A to city B on day X, then day X counts for both A and B.
    # Let city1 (Dublin) have planned days d1, city2 (Riga) have planned days d2, 
    # and city3 (Vilnius) have planned days d3.
    # The schedule is computed as:
    #   - City1: Day 1 to Day d1 
    #   - City2: Starts on the flight day from city1 (i.e. Day d1) and ends on Day (d1 + d2 - 1)
    #   - City3: Starts on the flight day from city2 (i.e. Day (d1 + d2 - 1)) and ends on Day (d1 + d2 + d3 - 2)
    d1 = planned_days[itinerary_order[0]]
    d2 = planned_days[itinerary_order[1]]
    d3 = planned_days[itinerary_order[2]]
    
    city1_start = 1
    city1_end = d1  # Flight day from Dublin to Riga is counted in Dublin, hence end = d1
    
    city2_start = city1_end  # Arrival day in Riga is the same as Dublin's departure day.
    city2_end = d1 + d2 - 1  # d2 includes both the arrival day and departure day.
    
    city3_start = city2_end  # Arrival day in Vilnius overlaps with Riga's departure day.
    city3_end = d1 + d2 + d3 - 2  # Total itinerary days
    
    # Check if the computed final day equals the total trip days.
    if city3_end != total_days:
        valid_itinerary = False

    # Construct the output itinerary if valid.
    output = {}
    if valid_itinerary:
        itinerary = [
            {"day_range": "Day {}-{}".format(city1_start, city1_end), "place": itinerary_order[0]},
            {"day_range": "Day {}-{}".format(city2_start, city2_end), "place": itinerary_order[1]},
            {"day_range": "Day {}-{}".format(city3_start, city3_end), "place": itinerary_order[2]}
        ]
        output["itinerary"] = itinerary
    else:
        output["error"] = "No valid itinerary found with the given constraints."
    
    # Output the result as a JSON-formatted dictionary.
    print(json.dumps(output))

if __name__ == '__main__':
    main()