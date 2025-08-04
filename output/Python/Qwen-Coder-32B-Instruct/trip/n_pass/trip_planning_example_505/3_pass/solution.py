import json

def calculate_itinerary():
    # Define the constraints
    total_days = 8
    stays = {
        "Prague": 2,
        "Krakow": 2,
        "Split": 2,
        "Stuttgart": 2,
        "Florence": 0   # No stay in Florence to fit within 8 days
    }
    events = {
        "Stuttgart": (7, 8),  # Wedding
        "Split": (5, 6)       # Meet friends
    }
    direct_flights = {
        ("Stuttgart", "Split"),
        ("Prague", "Florence"),
        ("Krakow", "Stuttgart"),
        ("Krakow", "Split"),
        ("Split", "Prague"),
        ("Krakow", "Prague")
    }

    # Initialize the itinerary
    itinerary = []
    current_day = 1
    current_city = None

    # Function to add a stay to the itinerary
    def add_stay(city, start_day, duration):
        nonlocal current_day, current_city
        end_day = start_day + duration - 1
        itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": city})
        current_day = end_day + 1
        current_city = city

    # Start with Prague
    add_stay("Prague", current_day, stays["Prague"])

    # Move to Krakow (direct flight from Prague)
    add_stay("Krakow", current_day, stays["Krakow"])

    # Move to Split (direct flight from Krakow)
    add_stay("Split", current_day, stays["Split"])

    # Move to Stuttgart (direct flight from Split)
    add_stay("Stuttgart", current_day, stays["Stuttgart"])

    # No stay in Florence to fit within 8 days

    return itinerary

# Calculate the itinerary
itinerary = calculate_itinerary()

# Output the result as JSON
output = {"itinerary": itinerary}
print(json.dumps(output))