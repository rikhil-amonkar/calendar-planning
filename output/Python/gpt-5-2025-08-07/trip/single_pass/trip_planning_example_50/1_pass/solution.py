if __name__ == "__main__":
    # Input variables based on the given constraints
    total_days = 12
    city_days = {
        "Vilnius": 4,
        "Munich": 3,
        "Mykonos": 7,
    }
    # Direct flights: "Munich and Mykonos" (bidirectional), and "from Vilnius to Munich" (directional)
    direct_flights = [
        ("Vilnius", "Munich"),
        ("Munich", "Mykonos"),
        ("Mykonos", "Munich"),
    ]

    result = plan_trip(total_days, city_days, direct_flights)
    print(json.dumps(result, ensure_ascii=False))