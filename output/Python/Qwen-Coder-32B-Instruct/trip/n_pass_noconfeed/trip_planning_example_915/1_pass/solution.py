import json

def calculate_itinerary():
    # Define the constraints
    total_days = 26
    stay_duration = {
        "Bucharest": 3,
        "Venice": 5,
        "Prague": 4,
        "Frankfurt": 5,
        "Zurich": 5,
        "Florence": 5,
        "Tallinn": 5
    }
    events = {
        "Venice": (22, 26),
        "Frankfurt": (12, 16),
        "Tallinn": (8, 12)
    }
    direct_flights = [
        ("Prague", "Tallinn"), ("Prague", "Zurich"), ("Florence", "Prague"),
        ("Frankfurt", "Bucharest"), ("Frankfurt", "Venice"), ("Prague", "Bucharest"),
        ("Bucharest", "Zurich"), ("Tallinn", "Frankfurt"), ("Zurich", "Florence"),
        ("Frankfurt", "Zurich"), ("Zurich", "Venice"), ("Florence", "Frankfurt"),
        ("Prague", "Frankfurt"), ("Tallinn", "Zurich")
    ]

    # Initialize the itinerary
    itinerary = []
    current_day = 1
    locations = ["Bucharest", "Frankfurt", "Prague", "Zurich", "Tallinn", "Florence", "Venice"]

    # Function to add a stay to the itinerary
    def add_stay(city, start_day, duration):
        nonlocal current_day
        end_day = start_day + duration - 1
        itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": city})
        current_day = end_day + 1

    # Start in Bucharest
    add_stay("Bucharest", current_day, stay_duration["Bucharest"])

    # Go to Frankfurt for the annual show
    add_stay("Frankfurt", current_day, stay_duration["Frankfurt"])

    # Go to Prague
    add_stay("Prague", current_day, stay_duration["Prague"])

    # Go to Zurich
    add_stay("Zurich", current_day, stay_duration["Zurich"])

    # Go to Tallinn to meet friends
    add_stay("Tallinn", current_day, stay_duration["Tallinn"] - (events["Tallinn"][1] - current_day + 1))
    add_stay("Tallinn", events["Tallinn"][0], events["Tallinn"][1] - events["Tallinn"][0] + 1)

    # Go to Florence
    add_stay("Florence", current_day, stay_duration["Florence"])

    # Go to Venice for the wedding
    add_stay("Venice", events["Venice"][0], events["Venice"][1] - events["Venice"][0] + 1)

    return {"itinerary": itinerary}

# Calculate and print the itinerary as JSON
print(json.dumps(calculate_itinerary()))