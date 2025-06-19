def main():
    flight_days = [2, 4, 6, 8, 10]
    cities = ["Helsinki", "Madrid", "Budapest", "Reykjavik", "Warsaw", "Split"]
    
    print("Day\tStart City\tFlight To\tCities Visited (during the day)")
    for day in range(1, 15):
        if day < flight_days[0]:
            start_city = cities[0]
            flight_str = "None"
            visited = [cities[0]]
        elif day == flight_days[0]:
            start_city = cities[0]
            flight_str = f"{cities[0]} to {cities[1]}"
            visited = [cities[0], cities[1]]
        elif day < flight_days[1]:
            start_city = cities[1]
            flight_str = "None"
            visited = [cities[1]]
        elif day == flight_days[1]:
            start_city = cities[1]
            flight_str = f"{cities[1]} to {cities[2]}"
            visited = [cities[1], cities[2]]
        elif day < flight_days[2]:
            start_city = cities[2]
            flight_str = "None"
            visited = [cities[2]]
        elif day == flight_days[2]:
            start_city = cities[2]
            flight_str = f"{cities[2]} to {cities[3]}"
            visited = [cities[2], cities[3]]
        elif day < flight_days[3]:
            start_city = cities[3]
            flight_str = "None"
            visited = [cities[3]]
        elif day == flight_days[3]:
            start_city = cities[3]
            flight_str = f"{cities[3]} to {cities[4]}"
            visited = [cities[3], cities[4]]
        elif day < flight_days[4]:
            start_city = cities[4]
            flight_str = "None"
            visited = [cities[4]]
        elif day == flight_days[4]:
            start_city = cities[4]
            flight_str = f"{cities[4]} to {cities[5]}"
            visited = [cities[4], cities[5]]
        else:
            start_city = cities[5]
            flight_str = "None"
            visited = [cities[5]]
        
        visited_str = ", ".join(visited)
        print(f"{day}\t{start_city}\t{flight_str}\t{visited_str}")

if __name__ == "__main__":
    main()