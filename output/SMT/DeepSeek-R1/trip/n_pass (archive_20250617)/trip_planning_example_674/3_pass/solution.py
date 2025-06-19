def main():
    cities = ["Helsinki", "Madrid", "Budapest", "Reykjavik", "Warsaw", "Split"]
    flight_schedule = {
        2: (0, 1),  # Helsinki to Madrid
        5: (1, 2),  # Madrid to Budapest
        8: (2, 3),  # Budapest to Reykjavik
        10: (3, 4), # Reykjavik to Warsaw
        12: (4, 5)  # Warsaw to Split
    }
    
    current_city = 0  # Start in Helsinki
    print("Day\tStart City\tFlight To\tCities Visited (during the day)")
    
    for day in range(1, 15):
        if day in flight_schedule:
            from_idx, to_idx = flight_schedule[day]
            start_city = cities[from_idx]
            flight_str = f"{cities[from_idx]} to {cities[to_idx]}"
            visited = [cities[from_idx], cities[to_idx]]
            current_city = to_idx
        else:
            start_city = cities[current_city]
            flight_str = "None"
            visited = [cities[current_city]]
        
        visited_str = ", ".join(visited)
        print(f"{day}\t{start_city}\t{flight_str}\t{visited_str}")

if __name__ == "__main__":
    main()