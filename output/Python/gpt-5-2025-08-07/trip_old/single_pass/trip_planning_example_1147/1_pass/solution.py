if __name__ == "__main__":
    # Input variables based on the problem statement
    total_days = 22
    durations = {
        "Brussels": 3,
        "Helsinki": 3,
        "Split": 4,
        "Dubrovnik": 2,
        "Istanbul": 5,
        "Milan": 4,
        "Vilnius": 5,
        "Frankfurt": 3
    }
    presence_windows = {
        # Must be in Istanbul for days 1-5 (annual show)
        "Istanbul": (1, 5),
        # Must be at wedding in Frankfurt days 16-18
        "Frankfurt": (16, 18),
        # Must attend workshop in Vilnius days 18-22
        "Vilnius": (18, 22)
    }
    flights_list = [
        "Milan and Frankfurt",
        "Split and Frankfurt",
        "Milan and Split",
        "Brussels and Vilnius",
        "Brussels and Helsinki",
        "Istanbul and Brussels",
        "Milan and Vilnius",
        "Brussels and Milan",
        "Istanbul and Helsinki",
        "Helsinki and Vilnius",
        "Helsinki and Dubrovnik",
        "Split and Vilnius",
        "from Dubrovnik to Istanbul",
        "Istanbul and Milan",
        "Helsinki and Frankfurt",
        "Istanbul and Vilnius",
        "Split and Helsinki",
        "Milan and Helsinki",
        "Istanbul and Frankfurt",
        "from Brussels to Frankfurt",
        "Dubrovnik and Frankfurt",
        "Frankfurt and Vilnius"
    ]

    result = compute_itinerary(total_days, durations, presence_windows, flights_list)
    print(json.dumps(result, ensure_ascii=False))