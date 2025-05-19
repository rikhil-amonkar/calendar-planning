import json

def compute_itinerary():
    # Input parameters
    total_days = 12
    cities = ["Brussels", "Barcelona", "Split"]
    duration_brussels = 2      # Must spend 2 days in Brussels (conference on day 1 and 2)
    duration_barcelona = 7     # Must spend 7 days in Barcelona
    duration_split = 5         # Must spend 5 days in Split

    # The flights are direct: Brussels <-> Barcelona and Barcelona <-> Split.
    # When flying from one city to another on a flight day, that day counts for both cities.
    # To meet the required individual city durations within a total of 12 days,
    # we plan to take the flights on the last day of Brussels and the last day of Barcelona.
    #
    # Let the flight from Brussels to Barcelona be on day = duration_brussels.
    # This day counts as the 2nd day in Brussels and also as the starting day in Barcelona.
    # Then Barcelona gets its full count if we add additional days.
    # Similarly, take the flight from Barcelona to Split on the last day of Barcelona count.
    #
    # Calculate flight days and segments:
    flight_day_1 = duration_brussels  # Brussels->Barcelona flight day (overlap day)
    # Barcelona already gets one day (flight day_1), so additional needed = duration_barcelona - 1.
    flight_day_2 = flight_day_1 + (duration_barcelona - 1)  # Barcelona->Split flight day (overlap day)
    # Split gets one day from the flight day_2 and needs extra.
    # Final day of Split stay = flight_day_2 + (duration_split - 1)
    final_day = flight_day_2 + (duration_split - 1)
    
    # Sanity check: final_day should be equal to total_days (12)
    if final_day != total_days:
        raise ValueError("The calculated itinerary does not sum up to total days.")
        
    itinerary = []
    
    # Brussels: from day 1 to flight_day_1 (inclusive) 
    brussels_range = f"1-{flight_day_1}"
    itinerary.append({"day_range": brussels_range, "place": "Brussels"})
    
    # Barcelona: from flight_day_1 (overlap flight day) to flight_day_2 (inclusive)
    barcelona_range = f"{flight_day_1}-{flight_day_2}"
    itinerary.append({"day_range": barcelona_range, "place": "Barcelona"})
    
    # Split: from flight_day_2 (overlap flight day) to final_day (inclusive)
    split_range = f"{flight_day_2}-{final_day}"
    itinerary.append({"day_range": split_range, "place": "Split"})
    
    return itinerary

if __name__ == "__main__":
    itinerary = compute_itinerary()
    # Output the itinerary in JSON format
    print(json.dumps(itinerary))