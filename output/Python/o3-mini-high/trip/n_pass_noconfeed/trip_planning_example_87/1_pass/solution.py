import json

def compute_itinerary(total_days, riga_days, amsterdam_days, mykonos_days, direct_flights):
    # In our case the only feasible ordering given connectivity and constraints is:
    # Riga (visit relatives between Day 1-2) -> Amsterdam -> Mykonos
    #
    # Note: When flying on a day, that day counts as a day in both departure and arrival cities.
    #
    # Let the flight from Riga to Amsterdam be on day F1 and the flight from Amsterdam to Mykonos on day F2.
    # Then:
    #   Days in Riga = F1 (since day 1 through F1 inclusive, F1 counts as both Riga and Amsterdam)
    #   Days in Amsterdam = F2 - F1 + 1 (because F1 and F2 are both counted)
    #   Days in Mykonos = total_days - F2 + 1 (since F2 counts as both Amsterdam and Mykonos)
    #
    # We require:
    #   Riga days = riga_days
    #   Amsterdam days = amsterdam_days
    #   Mykonos days = mykonos_days
    #
    # Solving:
    #   F1 = riga_days
    #   (F2 - F1 + 1) = amsterdam_days  => F2 = F1 + amsterdam_days - 1
    #   (total_days - F2 + 1) = mykonos_days  => total_days - (F1 + amsterdam_days - 1) + 1 = mykonos_days
    #
    # Check that the constraints match:
    #   total_days = (riga_days) + (amsterdam_days - 1) + (mykonos_days - 1)
    # For the given numbers: 7 = 2 + (2-1) + (5-1) = 2 + 1 + 4 = 7, so it works.
    
    flight_day1 = riga_days                 # Flight from Riga -> Amsterdam on this day.
    flight_day2 = flight_day1 + amsterdam_days - 1  # Flight from Amsterdam -> Mykonos on this day.
    
    # Verify direct flights exist for the planned route.
    route = [("Riga", "Amsterdam"), ("Amsterdam", "Mykonos")]
    for frm, to in route:
        if not (to in direct_flights.get(frm, [])):
            raise ValueError(f"No direct flight available from {frm} to {to}.")
    
    # Define segments:
    # Segment for Riga: Day 1 to flight_day1 (inclusive)
    # Segment for Amsterdam: Day flight_day1 to flight_day2 (inclusive)
    # Segment for Mykonos: Day flight_day2 to total_days (inclusive)
    itinerary_segments = []
    
    itinerary_segments.append({
        "day_range": f"Day 1-{flight_day1}",
        "place": "Riga"
    })
    itinerary_segments.append({
        "day_range": f"Day {flight_day1}-{flight_day2}",
        "place": "Amsterdam"
    })
    itinerary_segments.append({
        "day_range": f"Day {flight_day2}-{total_days}",
        "place": "Mykonos"
    })
    
    # Build result dictionary.
    result = {"itinerary": itinerary_segments}
    return result

def main():
    # Trip constraints and parameters:
    total_days = 7
    riga_days = 2       # Must spend 2 days in Riga
    amsterdam_days = 2  # Must spend 2 days in Amsterdam
    mykonos_days = 5    # Must spend 5 days in Mykonos
    # Direct flights connections: each key has list of cities with direct flight connection.
    direct_flights = {
        "Amsterdam": ["Mykonos", "Riga"],
        "Mykonos": ["Amsterdam"],
        "Riga": ["Amsterdam"]
    }
    
    # Compute the itinerary.
    itinerary = compute_itinerary(total_days, riga_days, amsterdam_days, mykonos_days, direct_flights)
    
    # Output the result as a JSON-formatted string.
    print(json.dumps(itinerary))

if __name__ == "__main__":
    main()