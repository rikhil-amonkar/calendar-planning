if __name__ == "__main__":
    # Input variables (trip constraints)
    total_days = 15
    city_durations = {
        "Stuttgart": 6,
        "Seville": 7,
        "Manchester": 4
    }
    direct_flight_pairs = [
        ("Manchester", "Seville"),
        ("Stuttgart", "Manchester")
    ]
    friend_city = "Stuttgart"
    meet_window = (1, 6)  # inclusive

    result = find_itinerary(total_days, city_durations, direct_flight_pairs, friend_city, meet_window)
    print(json.dumps(result))