import json

def calculate_itinerary():
    # Define the constraints
    total_days = 16
    city_stays = {
        "Dubrovnik": 4,
        "Split": 3,
        "Milan": 3,
        "Porto": 4,
        "Krakow": 2,
        "Munich": 5
    }
    events = {
        "Milan": (11, 13),
        "Krakow": (8, 9),
        "Munich": (4, 8)
    }

    # Initialize the itinerary
    itinerary = []
    current_day = 1

    # Helper function to add a stay to the itinerary
    def add_stay(city, start_day, end_day):
        nonlocal itinerary
        itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": city})

    # Start with Dubrovnik
    add_stay("Dubrovnik", current_day, current_day + city_stays["Dubrovnik"] - 1)
    current_day += city_stays["Dubrovnik"]

    # Move to Munich for the show
    add_stay("Munich", current_day, events["Munich"][1])
    current_day = events["Munich"][1] + 1

    # Move to Krakow to meet friends
    add_stay("Krakow", current_day, events["Krakow"][1])
    current_day = events["Krakow"][1] + 1

    # Move to Milan for the wedding
    add_stay("Milan", current_day, events["Milan"][1])
    current_day = events["Milan"][1] + 1

    # Move to Split
    add_stay("Split", current_day, current_day + city_stays["Split"] - 1)
    current_day += city_stays["Split"]

    # Move to Porto
    add_stay("Porto", current_day, total_days)

    # Output the itinerary as JSON
    return json.dumps({"itinerary": itinerary})

# Run the function and print the result
print(calculate_itinerary())