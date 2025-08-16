import json

def calculate_itinerary():
    # Define the constraints
    total_days = 18
    stays = {
        "Helsinki": 4,
        "Valencia": 5,
        "Dubrovnik": 4,
        "Porto": 3,
        "Prague": 3,
        "Reykjavik": 4
    }
    friend_meeting_days = range(16, 19)
    direct_flights = {
        "Helsinki": ["Prague", "Reykjavik", "Dubrovnik"],
        "Prague": ["Helsinki", "Valencia"],
        "Valencia": ["Prague", "Porto"],
        "Porto": ["Valencia"],
        "Reykjavik": ["Helsinki", "Prague"],
        "Dubrovnik": ["Helsinki"]
    }

    # Initialize the itinerary
    itinerary = []
    current_day = 1
    current_city = "Helsinki"
    itinerary.append({"day_range": f"Day {current_day}-{current_day + stays[current_city] - 1}", "place": current_city})
    current_day += stays[current_city]

    # Plan the rest of the itinerary
    def find_next_city(current_city, current_day):
        for city, duration in stays.items():
            if city != current_city and duration > 0:
                for next_city in direct_flights[current_city]:
                    if next_city == city and (city != "Porto" or current_day + duration - 1 in friend_meeting_days):
                        return city
        return None

    while current_day < total_days:
        next_city = find_next_city(current_city, current_day)
        if next_city:
            itinerary.append({"day_range": f"Day {current_day}-{current_day + stays[next_city] - 1}", "place": next_city})
            current_day += stays[next_city]
            current_city = next_city
        else:
            break

    # Ensure the friend meeting constraint is met
    porto_stay = next((item for item in itinerary if item["place"] == "Porto"), None)
    if porto_stay:
        start_day, end_day = map(int, porto_stay["day_range"].replace("Day ", "").split("-"))
        if not any(day in friend_meeting_days for day in range(start_day, end_day + 1)):
            # Adjust the Porto stay to meet the friend
            new_start_day = max(friend_meeting_days) - stays["Porto"] + 1
            porto_stay["day_range"] = f"Day {new_start_day}-{max(friend_meeting_days)}"

    return itinerary

# Calculate and output the itinerary
itinerary_result = calculate_itinerary()
print(json.dumps({"itinerary": itinerary_result}))