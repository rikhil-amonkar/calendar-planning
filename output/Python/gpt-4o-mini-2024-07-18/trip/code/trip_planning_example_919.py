import json

# Input parameters
days_total = 15
cities = {
    "Vienna": {"days": 4, "conference_days": [1, 4]},
    "Milan": {"days": 2},
    "Rome": {"days": 3},
    "Riga": {"days": 2},
    "Lisbon": {"days": 3, "relatives_days": [11, 12, 13]},
    "Vilnius": {"days": 4},
    "Oslo": {"days": 3, "friend_days": [13, 14, 15]}
}

direct_flights = {
    "Riga": ["Oslo", "Milan", "Vienna", "Lisbon"],
    "Oslo": ["Rome", "Milan", "Lisbon", "Vienna", "Vilnius"],
    "Rome": ["Riga", "Lisbon", "Oslo"],
    "Vienna": ["Milan", "Vilnius", "Lisbon", "Riga", "Rome"],
    "Milan": ["Oslo", "Vienna", "Riga", "Lisbon"],
    "Vilnius": ["Oslo", "Vienna", "Riga", "Milan"],
    "Lisbon": ["Oslo", "Vienna", "Riga", "Milan", "Rome"]
}

itinerary = []
current_day = 1

# Implementing the trip plan creation
def add_city_to_itinerary(city, start_day, duration):
    itinerary.append({"day_range": f"Day {start_day}-{start_day + duration - 1}", "place": city})

def add_flight_to_itinerary(from_city, to_city, flight_day):
    itinerary.append({"flying": f"Day {flight_day}-{flight_day}", "from": from_city, "to": to_city})

# Step 1: Start in Vienna for the conference and tourism
add_city_to_itinerary("Vienna", current_day, 4)
current_day += 4

# Step 2: Move to Milan (direct flight from Vienna)
add_flight_to_itinerary("Vienna", "Milan", current_day)
current_day += 1
add_city_to_itinerary("Milan", current_day, 2)
current_day += 2

# Step 3: Travel to Rome (direct flight from Milan)
add_flight_to_itinerary("Milan", "Rome", current_day)
current_day += 1
add_city_to_itinerary("Rome", current_day, 3)
current_day += 3

# Step 4: Go to Riga (direct flight from Rome)
add_flight_to_itinerary("Rome", "Riga", current_day)
current_day += 1
add_city_to_itinerary("Riga", current_day, 2)
current_day += 2

# Step 5: Travel to Lisbon (direct flight from Riga)
add_flight_to_itinerary("Riga", "Lisbon", current_day)
current_day += 1
add_city_to_itinerary("Lisbon", current_day, 3)
current_day += 3

# Step 6: Visit relatives in Lisbon (already within the Lisbon stay)

# Step 7: Move to Vilnius (direct flight from Lisbon)
add_flight_to_itinerary("Lisbon", "Vilnius", current_day)
current_day += 1
add_city_to_itinerary("Vilnius", current_day, 4)
current_day += 4

# Step 8: Finally, fly to Oslo (direct flight from Vilnius)
add_flight_to_itinerary("Vilnius", "Oslo", current_day)
current_day += 1
add_city_to_itinerary("Oslo", current_day, 3)

# Output the final itinerary in JSON format
output_json = json.dumps(itinerary, indent=4)
print(output_json)