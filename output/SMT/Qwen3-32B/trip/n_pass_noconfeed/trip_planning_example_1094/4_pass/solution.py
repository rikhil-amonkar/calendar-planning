cities = ["Paris", "London", "New York", "Tokyo", "Sydney", "Rio", "Cape Town", "Dubai"]
for city_index, city in enumerate(cities):
    result = 2 if city_index == 7 else 0
    print(f"City: {city}, Result: {result}")