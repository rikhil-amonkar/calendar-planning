import json

def create_itinerary():
    # Input parameters
    constraints = {
        "Lyon": {"days": 3},
        "Paris": {"days": 5},
        "Riga": {"days": 2},
        "Berlin": {"days": 2, "wedding_days": [1, 2]},
        "Stockholm": {"days": 3, "show_days": [20, 21, 22]},
        "Zurich": {"days": 5},
        "Nice": {"days": 2, "workshop_days": [12, 13]},
        "Seville": {"days": 3},
        "Milan": {"days": 3},
        "Naples": {"days": 4}
    }
    
    # Total days of the trip
    total_days = 23
    current_day = 1
    itinerary = []
    
    # Planning the itinerary
    def add_to_itinerary(place, start_day, days):
        end_day = start_day + days - 1
        itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": place})
        return end_day + 1  # next starting day after the stay

    # Start planning
    current_day = add_to_itinerary("Berlin", current_day, 2)  # Wedding days on Day 1 and 2

    current_day = add_to_itinerary("Lyon", current_day, 3)    # Visit Lyon for 3 days
    
    current_day = add_to_itinerary("Paris", current_day, 5)   # Visit Paris for 5 days

    current_day = add_to_itinerary("Nice", current_day, 2)     # Workshop in Nice between Day 12-13
    
    # Workshop days need handling in this order
    add_to_itinerary("Nice", 12, 2)  # Stay in Nice for the workshop
    
    current_day += 1  # Move to the next day after the workshop
    
    current_day = add_to_itinerary("Riga", current_day, 2)    # Stay in Riga for 2 days

    current_day = add_to_itinerary("Berlin", current_day, 2)  # Return to Berlin for 2 more days

    current_day = add_to_itinerary("Stockholm", current_day, 3)  # Stay in Stockholm for 3 days

    # Annual show in Stockholm
    current_day = add_to_itinerary("Stockholm", 20, 3)  # From day 20 to day 22 for the show

    current_day = add_to_itinerary("Zurich", current_day, 5)    # Visit Zurich for 5 days

    current_day = add_to_itinerary("Seville", current_day, 3)    # Visit Seville for 3 days

    current_day = add_to_itinerary("Milan", current_day, 3)      # Stay in Milan for 3 days

    current_day = add_to_itinerary("Naples", current_day, 4)     # Visit Naples for 4 days

    # Output the completed itinerary
    return json.dumps(itinerary, indent=4)

# Run the function and print the result
if __name__ == "__main__":
    travel_plan = create_itinerary()
    print(travel_plan)