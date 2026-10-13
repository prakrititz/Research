# Derivation of verina_advanced_72

kind: **restate**

- **cases** on `n = 0`
  - _then_:
    - **term**: `0`
  - _else_:
    - **cases** on `n % 2 = 0`
      - _then_:
        - **term**: `2`
      - _else_:
        - **cases** on `n % 3 = 0`
          - _then_:
            - **term**: `3`
          - _else_:
            - **cases** on `n % 5 = 0`
              - _then_:
                - **term**: `5`
              - _else_:
                - **cases** on `n % 7 = 0`
                  - _then_:
                    - **term**: `7`
                  - _else_:
                    - **term**: `0`
