if __name__ == "__main__":
    # Input variables (trip constraints)
    total_days = 21
    cities = ["Manchester", "Istanbul", "Venice", "Krakow", "Lyon"]
    durations = {
        "Manchester": 3,
        "Istanbul": 7,
        "Venice": 7,
        "Krakow": 6,
        "Lyon": 2
    }
    flights = [
        ("Manchester", "Venice"),
        ("Manchester", "Istanbul"),
        ("Venice", "Istanbul"),
        ("Istanbul", "Krakow"),
        ("Venice", "Lyon"),
        ("Lyon", "Istanbul"),
        ("Manchester", "Krakow")
    ]
    wedding_city = "Manchester"
    wedding_window = (1, 3)  # inclusive
    workshop_city = "Venice"
    workshop_window = (3, 9)  # inclusive

    result = generate_itinerary(
        cities=cities,
        durations=durations,
        total_days=total_days,
        flights=flights,
        wedding_city=wedding_city,
        wedding_window=wedding_window,
        workshop_city=workshop_city,
        workshop_window=workshop_window
    )

    print(json.dumps(result))