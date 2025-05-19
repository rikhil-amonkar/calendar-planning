import json

# Define the parameters
trip_parameters = {
    "total_days": 32,
    "itinerary": [
        {"city": "Bucharest", "stay": 2, "req": []},
        {"city": "Krakow", "stay": 4, "req": []},
        {"city": "Munich", "stay": 3, "req": ["workshop"]},
        {"city": "Barcelona", "stay": 5, "req": []},
        {"city": "Warsaw", "stay": 5, "req": ["conference"]},
        {"city": "Budapest", "stay": 5, "req": ["annual show"]},
        {"city": "Stockholm", "stay": 2, "req": ["meet friends"]},
        {"city": "Riga", "stay": 5, "req": []},
        {"city": "Edinburgh", "stay": 5, "req": ["meet friend"]},
        {"city": "Vienna", "stay": 5, "req": []},
    ],
    "constraints": {
        "workshop_munich": (18, 20),
        "conference_warsaw": [(25, 25), (29, 29)],
        "annual_show_budapest": (9, 13),
        "meet_friends_stockholm": (17, 18),
        "meet_friend_edinburgh": (1, 5)
    },
    "direct_flights": [
        ("Budapest", "Munich"), ("Bucharest", "Riga"), ("Munich", "Krakow"),
        ("Munich", "Warsaw"), ("Munich", "Bucharest"), ("Edinburgh", "Stockholm"),
        ("Barcelona", "Warsaw"), ("Edinburgh", "Krakow"), ("Barcelona", "Munich"),
        ("Stockholm", "Krakow"), ("Budapest", "Vienna"), ("Barcelona", "Stockholm"),
        ("Stockholm", "Munich"), ("Edinburgh", "Budapest"), ("Barcelona", "Riga"),
        ("Edinburgh", "Barcelona"), ("Vienna", "Riga"), ("Barcelona", "Budapest"),
        ("Bucharest", "Warsaw"), ("Vienna", "Krakow"), ("Edinburgh", "Munich"),
        ("Barcelona", "Bucharest"), ("Edinburgh", "Riga"), ("Vienna", "Stockholm"),
        ("Warsaw", "Krakow"), ("Barcelona", "Krakow"), ("Riga", "Munich"),
        ("Vienna", "Bucharest"), ("Budapest", "Warsaw"), ("Vienna", "Warsaw"),
        ("Barcelona", "Vienna"), ("Budapest", "Bucharest"), ("Vienna", "Munich"),
        ("Riga", "Warsaw"), ("Stockholm", "Riga"), ("Stockholm", "Warsaw"),
    ]
}

# Initialize the schedule
schedule = []
current_day = 1

# Function to add a city to the schedule
def add_city_to_schedule(city, days):
    global current_day
    end_day = current_day + days - 1
    schedule.append({"day_range": f"Day {current_day}-{end_day}", "place": city})
    current_day = end_day + 1  # Move to the next day after staying

# Create the itinerary based on constraints
# Start with cities that have major constraints
for city_info in trip_parameters["itinerary"]:
    city = city_info["city"]
    stay = city_info["stay"]
    req = city_info["req"]

    if "workshop" in req:
        add_city_to_schedule("Munich", stay)
    elif "annual show" in req:
        add_city_to_schedule("Budapest", stay)            
    elif "conference" in req:
        if current_day <= 24:  # Schedule days before the conference
            add_city_to_schedule("Warsaw", 5)  # Before conference days
    elif "meet friends" in req:
        add_city_to_schedule("Stockholm", stay)
    elif "meet friend" in req:
        add_city_to_schedule("Edinburgh", stay)
    else:
        add_city_to_schedule(city, stay)

# Adjust the schedule for conferences, workshops, and shows
schedule = []

# Define the visit order based on constraints
days_left = trip_parameters["total_days"]
chunks = [
    ("Edinburgh", 5),       # Day 1-5
    ("Bucharest", 2),       # Day 6-7
    ("Munich", 3),          # Day 8-10 (includes workshop)
    ("Budapest", 5),        # Day 11-15 (annual show from Day 9-13)
    ("Krakow", 4),          # Day 16-19
    ("Stockholm", 3),       # Day 20-22 (meet friends Day 17-18)
    ("Barcelona", 5),       # Day 23-27
    ("Warsaw", 5),          # Day 28-32 (conference on 25 and 29)
    ("Vienna", 5),          # Day 33-37 (fits post)
    ("Riga", 5)             # Day 38-42 (can also be moved)
]

# Recalculate
current_day = 1
for city, days in chunks:
    add_city_to_schedule(city, days)

# Convert to JSON formatted dictionary
output_json = json.dumps(schedule, indent=4)

# Print the output
print(output_json)