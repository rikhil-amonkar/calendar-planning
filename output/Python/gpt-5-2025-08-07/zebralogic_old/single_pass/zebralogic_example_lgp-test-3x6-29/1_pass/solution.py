if __name__ == "__main__":
    res = solve()
    if res is None:
        # Fallback to ensure valid JSON output even if no solution found
        print(json.dumps({"solution": {"header": ["House", "Name", "Animal", "Birthday", "Hobby", "Drink", "HairColor"], "rows": []}}))
    else:
        print(json.dumps(res))