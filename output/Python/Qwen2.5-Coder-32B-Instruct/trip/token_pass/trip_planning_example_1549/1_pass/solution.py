import json

# Define the constraints
constraints = {
    "Prague": 5,
    "Tallinn": 3,
    "Tallinn_dates": (18, 20),
    "Warsaw": 2,
    "Porto": 3,
    "Naples": 5,
    "Milan": 3,
    "Milan_dates": (24, 26),
    "Lisbon": 5,
    "Santorini": 5,
    "Riga": 4,
    "Riga_dates": (5, 8),
    "Stockholm": 2
}

# Define the direct flights
direct_flights = {
    ("Riga", "Prague"), ("Stockholm", "Milan"), ("Riga", "Milan"),
    ("Lisbon", "Stockholm"), ("Stockholm", "Santorini"), ("Naples", "Warsaw"),
    ("Lisbon", "Warsaw"), ("Naples", "Milan"), ("Lisbon", "Naples"),
    ("Riga", "Tallinn"), ("Tallinn", "Prague"), ("Stockholm", "Warsaw"),
    ("Riga", "Warsaw"), ("Lisbon", "Riga"), ("Riga", "Stockholm"),
    ("Lisbon", "Porto"), ("Lisbon", "Prague"), ("Milan", "Porto"),
    ("Prague", "Milan"), ("Lisbon", "Milan"), ("Warsaw", "Porto"),
    ("Warsaw", "Tallinn"), ("Santorini", "Milan"), ("Stockholm", "Prague"),
    ("Stockholm", "Tallinn"), ("Warsaw", "Milan"), ("Santorini", "Naples"),
    ("Warsaw", "Prague")
}

# Initialize the itinerary
itinerary = []

# Function to add a stay to the itinerary
def add_stay(city, start_day, end_day):
    itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": city})

# Place fixed stays
add_stay("Riga", 5, 8)  # Riga: Days 5-8
add_stay("Tallinn", 18, 20)  # Tallinn: Days 18-20
add_stay("Milan", 24, 26)  # Milan: Days 24-26

# Place other stays considering constraints and direct flights
current_day = 1

# Start in Riga (Days 1-4)
if current_day < 5:
    add_stay("Riga", current_day, 4)
    current_day = 5

# Move to Prague (Days 9-13)
if current_day == 5:
    add_stay("Prague", current_day, 9)
    current_day = 10

# Move to Warsaw (Days 14-15)
if current_day == 10:
    add_stay("Warsaw", current_day, 11)
    current_day = 12

# Move to Tallinn (Days 12-17)
if current_day == 12:
    add_stay("Tallinn", current_day, 17)
    current_day = 18

# Tallinn is already fixed for Days 18-20
current_day = 21

# Move to Lisbon (Days 21-25)
if current_day == 21:
    add_stay("Lisbon", current_day, 25)
    current_day = 26

# Milan is already fixed for Days 24-26
current_day = 27

# Move to Porto (Days 27-29)
if current_day == 27:
    add_stay("Porto", current_day, 29)
    current_day = 30

# Move to Naples (Days 30-34)
if current_day == 30:
    add_stay("Naples", current_day, 34)
    current_day = 35

# Move to Santorini (Days 35-39)
if current_day == 35:
    add_stay("Santorini", current_day, 39)
    current_day = 40

# Adjust itinerary to fit 28 days
final_itinerary = []
current_day = 1

# Add adjusted stays
for entry in itinerary:
    day_range = entry["day_range"].split("-")
    start_day = int(day_range[0].split()[1])
    end_day = int(day_range[1])
    
    # Adjust for 28 days
    if start_day < current_day:
        start_day = current_day
        end_day = start_day + constraints[entry["place"]] - 1
    
    final_itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": entry["place"]})
    current_day = end_day + 1

# Ensure the last day is 28
last_entry = final_itinerary[-1]
day_range = last_entry["day_range"].split("-")
start_day = int(day_range[0].split()[1])
end_day = int(day_range[1])

if end_day > 28:
    end_day = 28
    final_itinerary[-1]["day_range"] = f"Day {start_day}-{end_day}"

# Output the itinerary as JSON
output = {"itinerary": final_itinerary}
print(json.dumps(output, indent=4))