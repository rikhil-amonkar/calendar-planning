if __name__ == "__main__":
    # Input variables based on the given constraints
    total_days = 12
    city_stays = {
        "Riga": 5,
        "Vilnius": 7,
        "Dublin": 2
    }
    # Direct flights: "Dublin and Riga" (both directions), and "from Riga to Vilnius"
    direct_flights = {
        "Dublin": ["Riga"],
        "Riga": ["Dublin", "Vilnius"],
        "Vilnius": []
    }

    result = find_itinerary(total_days, city_stays, direct_flights)
    print(json.dumps(result, ensure_ascii=False))